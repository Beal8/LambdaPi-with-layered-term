open Types

module Take = struct
  type ('a, 'b, 'c) action =
    | Rec of 'a list
    | Skip
    | Accum of 'b list
    | Stop_and_keep
    | Stop_and_accum of 'b list * 'c option

  let until ~classify items =
    let rec loop acc = function
      | [] -> (List.rev acc, None, [])
      | b :: rest -> (
          match classify b with
          | Skip -> loop acc rest
          | Rec x -> loop acc (x @ rest)
          | Accum v -> loop (List.rev_append v acc) rest
          | Stop_and_keep -> (List.rev acc, None, b :: rest)
          | Stop_and_accum (v, e) -> (List.rev_append acc v, e, rest))
    in
    loop [] items
end

module Rewire = struct
  type ('a, 'h) action = Rec of 'a | Skip | Heading of 'h * int

  let walk ~classify ~node items =
    let rec loop current_level acc l =
      match l with
      | [] -> (List.rev acc, [])
      | b :: rest -> (
          match classify b with
          | Skip -> loop current_level acc rest
          | Rec l -> loop current_level acc (l @ rest)
          | Heading (h, level) ->
              if level > current_level then
                let children, rest = loop level [] rest in
                loop current_level (node h children :: acc) rest
              else (List.rev acc, l))
    in
    let trees, rest = loop (-1) [] items in
    assert (rest = []);
    trees
end

module Toc : sig
  type t = one list

  and one = { url : Url.t; text : Inline.t; children : t }

  val compute :
    Url.Path.t -> on_sub:(Include.status -> bool) -> Item.t list -> t
end = struct
  type t = one list

  and one = { url : Url.t; text : Inline.t; children : t }

  let classify ~on_sub (i : Item.t) : _ Rewire.action =
    match i with
    | Text _ | Declaration _ -> Skip
    | Include { content = { status; content; _ }; _ } ->
        if on_sub status then Rec content else Skip
    | Heading { label = None; _ } -> Skip
    | Heading { label = Some label; level; title } ->
        Heading ((label, title), level)

  let node mkurl (anchor, text) children =
    { url = mkurl anchor; text; children }

  let compute page ~on_sub t =
    let mkurl anchor = { Url.Anchor.page; anchor; kind = `LeafPage } in
    Rewire.walk ~classify:(classify ~on_sub) ~node:(node mkurl) t
end

module Subpages : sig
  val compute : Page.t -> Subpage.t list
end = struct
  let rec walk_documentedsrc (l : DocumentedSrc.t) =
    Utils.flatmap l ~f:(function
      | DocumentedSrc.Code _ -> []
      | Documented _ -> []
      | Nested { code; _ } -> walk_documentedsrc code
      | Subpage p -> [ p ]
      | Alternative (Expansion r) -> walk_documentedsrc r.expansion)

  let rec walk_items (l : Item.t list) =
    Utils.flatmap l ~f:(function
      | Item.Text _ -> []
      | Heading _ -> []
      | Declaration { content; _ } -> walk_documentedsrc content
      | Include i -> walk_items i.content.content)

  let compute (p : Page.t) = walk_items (p.header @ p.items)
end

module Shift = struct
  type state = { englobing_level : int; current_level : int }

  let start = { englobing_level = 0; current_level = 0 }

  let shift st x =
    let level = st.englobing_level + x in
    ({ st with current_level = level }, level)

  let enter { current_level; _ } i =
    { englobing_level = current_level + i; current_level }

  let rec walk_documentedsrc ~on_sub shift_state (l : DocumentedSrc.t) =
    match l with
    | [] -> []
    | ((Code _ | Documented _) as h) :: rest ->
        h :: walk_documentedsrc ~on_sub shift_state rest
    | Nested ds :: rest ->
        let ds =
          { ds with code = walk_documentedsrc ~on_sub shift_state ds.code }
        in
        Nested ds :: walk_documentedsrc ~on_sub shift_state rest
    | Subpage subp :: rest ->
        let subp = subpage ~on_sub shift_state subp in
        Subpage subp :: walk_documentedsrc ~on_sub shift_state rest
    | Alternative (Expansion r) :: rest ->
        let expansion = walk_documentedsrc ~on_sub shift_state r.expansion in
        Alternative (Expansion { r with expansion })
        :: walk_documentedsrc ~on_sub shift_state rest

  and subpage ~on_sub shift_state (subp : Subpage.t) =
    match on_sub (`Page subp) with
    | None -> subp
    | Some i ->
        let shift_state = enter shift_state i in
        let page = subp.content in
        let content =
          {
            page with
            header = walk_item ~on_sub shift_state page.header;
            items = walk_item ~on_sub shift_state page.items;
          }
        in
        { subp with content }

  and include_ ~on_sub shift_state (subp : Include.t) =
    match on_sub (`Include subp) with
    | None -> subp
    | Some i ->
        let shift_state = enter shift_state i in
        let content = walk_item ~on_sub shift_state subp.content in
        { subp with content }

  and walk_item ~on_sub shift_state (l : Item.t list) =
    match l with
    | [] -> []
    | Heading { label; level; title } :: rest ->
        let shift_state, level = shift shift_state level in
        Item.Heading { label; level; title }
        :: walk_item ~on_sub shift_state rest
    | Include subp :: rest ->
        let content = include_ ~on_sub shift_state subp.content in
        let subp = { subp with content } in
        Item.Include subp :: walk_item ~on_sub shift_state rest
    | Declaration decl :: rest ->
        let decl =
          {
            decl with
            content = walk_documentedsrc ~on_sub shift_state decl.content;
          }
        in
        Declaration decl :: walk_item ~on_sub shift_state rest
    | Text txt :: rest -> Text txt :: walk_item ~on_sub shift_state rest

  let compute ~on_sub i =
    let shift_state = start in
    walk_item ~on_sub shift_state i
end

module Headings : sig
  val fold : ('a -> Heading.t -> 'a) -> 'a -> Page.t -> 'a
  (** Fold over every headings, follow subpages, nested documentedsrc and
      expansions. *)

  val foldmap :
    ('a -> Heading.t -> 'a * Heading.t) -> 'a -> Page.t -> 'a * Page.t
end = struct
  let fold =
    let rec w_page f acc page =
      w_items f (w_items f acc page.Page.header) page.items
    and w_items f acc ts = List.fold_left (w_item f) acc ts
    and w_item f acc = function
      | Heading h -> f acc h
      | Text _ -> acc
      | Declaration t -> w_documentedsrc f acc t.Item.content
      | Include t -> w_items f acc t.Item.content.content
    and w_documentedsrc f acc t = List.fold_left (w_documentedsrc_one f) acc t
    and w_documentedsrc_one f acc = function
      | DocumentedSrc.Code _ | Documented _ -> acc
      | Nested t -> w_documentedsrc f acc t.code
      | Subpage sp -> w_page f acc sp.content
      | Alternative (Expansion exp) -> w_documentedsrc f acc exp.expansion
    in
    w_page

  let rec foldmap_left f acc rlst = function
    | [] -> (acc, List.rev rlst)
    | hd :: tl ->
        let acc, hd = f acc hd in
        foldmap_left f acc (hd :: rlst) tl

  let foldmap_left f acc lst = foldmap_left f acc [] lst

  let foldmap =
    let rec w_page f acc page =
      let acc, header = w_items f acc page.Page.header in
      let acc, items = w_items f acc page.items in
      (acc, { page with header; items })
    and w_items f acc items = foldmap_left (w_item f) acc items
    and w_item f acc = function
      | Heading h ->
          let acc, h = f acc h in
          (acc, Heading h)
      | Text _ as x -> (acc, x)
      | Declaration t ->
          let acc, content = w_documentedsrc f acc t.content in
          (acc, Declaration { t with content })
      | Include t ->
          let acc, content = w_items f acc t.Item.content.content in
          (acc, Include { t with content = { t.content with content } })
    and w_documentedsrc f acc t = foldmap_left (w_documentedsrc_one f) acc t
    and w_documentedsrc_one f acc = function
      | (Code _ | Documented _) as x -> (acc, x)
      | Nested t ->
          let acc, code = w_documentedsrc f acc t.code in
          (acc, Nested { t with code })
      | Subpage sp ->
          let acc, content = w_page f acc sp.content in
          (acc, Subpage { sp with content })
      | Alternative (Expansion exp) ->
          let acc, expansion = w_documentedsrc f acc exp.expansion in
          (acc, Alternative (Expansion { exp with expansion }))
    in
    w_page
end

module Labels : sig
  val disambiguate_page : Page.t -> Page.t
  (** Colliding labels are allowed in the model but don't make sense in
      generators because we need to link to everything (eg. the TOC).
      Post-process the doctree, add a "_N" suffix to dupplicates, the first
      occurence is unchanged. Iterate through subpages. *)
end = struct
  module StringMap = Map.Make (String)

  let rec make_label_unique labels di label =
    let label' = label ^ "_" in
    (* start at [_2]. *)
    let new_label = label' ^ string_of_int (di + 1) in
    (* If the label is still ambiguous after suffixing, add an extra '_'. *)
    if StringMap.mem new_label labels then make_label_unique labels di label'
    else new_label

  let disambiguate_page page =
    (* Perform two passes, we need to know every labels before allocating new
        ones. *)
    let labels =
      Headings.fold
        (fun acc h ->
          match h.label with Some l -> StringMap.add l 0 acc | None -> acc)
        StringMap.empty page
    in
    Headings.foldmap
      (fun acc h ->
        match h.label with
        | Some l ->
            let d_index = StringMap.find l acc in
            let h =
              if d_index = 0 then h
              else
                let label = Some (make_label_unique acc d_index l) in
                { h with label }
            in
            (StringMap.add l (d_index + 1) acc, h)
        | None -> (acc, h))
      labels page
    |> snd
end