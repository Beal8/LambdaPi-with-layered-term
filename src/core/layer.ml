open Term
open Printf
open Bindlib
open Timed

let i = ref 0

let dcr i =
  i := !i - 1;
  !i

let reset i = i := 0

type ltvar = layered_term var

and ltbinder = (layered_term, layered_term) binder

and layered_term =
  | LVari of ltvar * int (** Free variable. *)
  | LType of int (** "TYPE" constant. *)
  | LKind of int (** "KIND" constant. *)
  | LProd of layered_term * ltbinder * int (** Dependent product. *)
  | LAbst of layered_term * ltbinder * int (** Abstraction. *)
  | LAppl of layered_term * layered_term * int (** Term application. *)
  | LSymb of lsym * int list (**Layered symbol*)

and lsym =
  { sym_expo  : expo (** Visibility. Private Public ...*)
  ; sym_path  : Common.Path.t (** Module in which the symbol is defined. *)
  ; sym_name  : string (** Name. *)
  ; sym_type  : term ref (** Type. *)
  ; sym_layer : expr (** Layer declaration. *)
  ; sym_impl  : bool list (** Implicit arguments ([true] meaning implicit). ex add {A}->A->A->A*)
  ; sym_prop  : prop (** Property. *)
  ; sym_def   : term option ref (** Definition with ≔. *)
  ; sym_opaq  : bool (** Opacity. *)
  ; sym_rules : rule list ref (** Rewriting rules. *)
  ; sym_mstrat: match_strat (** Matching strategy. *)
  ; sym_dtree : dtree ref (** Decision tree used for matching. *) }

and expr =
  | Var of expr var
  | Fun of expr*expr
  | Zero
  | Succ : expr -> expr
  | Add : expr*expr -> expr

let mk_free_evar = fun x -> Var x

let rec expr_of_int i =
  if i == 0 then Zero else Succ(expr_of_int (i-1))

(*Parse expression (layer declaration of a symbol) from string*)
let parse : string -> expr = fun s ->
  let normalize = fun s -> Str.global_replace (Str.regexp " ") "" s in
  let s = normalize s in
  let s = Str.global_replace (Str.regexp "->") "/"  s in
  let ls = String.split_on_char '/' s in
  let rec aux acc vars = function
    |[] -> acc
    |'+'::c::q -> let c,vars_ = try expr_of_int (int_of_string (String.make 1 c)), vars with _ -> begin let name = String.make 1 c in let v = try List.assoc name vars with _ -> (new_var mk_free_evar (name)) in Var v, ((name_of v,v)::vars) end in aux (Add(fst acc,c),vars_) vars_ q
    |c::q when not (c = '+')-> let c,vars_ = try expr_of_int (int_of_string (String.make 1 c)),vars with _ -> begin let name = String.make 1 c in let v = try List.assoc name vars with _ -> (new_var mk_free_evar (String.make 1 c)) in (Var v),((name_of v,v)::vars) end in aux (c,vars_) vars_ q
    |_ -> failwith "couldn't parse the expr" in
  let explode s = List.init (String.length s) (String.get s) in
  let rec apply_aux vars = function
    |[] -> []
    |t::q -> let e,vars_ = aux (Zero,vars) vars t in e::(apply_aux vars_ q) in
  let le = apply_aux [] (List.map (fun s -> explode s) ls) in
  List.fold_left (fun acc e -> Fun(acc,e)) (List.hd le) (List.tl le)

let rec print_expr = function
  |Var v -> sprintf "(%s,%i)" (name_of v) (uid_of v)
  |Fun (a,b) -> (print_expr a) ^ "->" ^ (print_expr b)
  |Zero -> "0"
  |Succ (e) -> "Succ (" ^ (print_expr e) ^ ")"
  |Add (a,b) -> (print_expr a) ^ "+" ^(print_expr b)




let sym_to_lsym : sym -> expr-> lsym = fun s e ->
  { sym_expo = s.sym_expo;
    sym_path = s.sym_path;
    sym_name = s.sym_name;
    sym_type = s.sym_type;
    sym_layer = e;
    sym_impl = s.sym_impl;
    sym_prop = s.sym_prop;
    sym_def = s.sym_def;
    sym_opaq = s.sym_opaq;
    sym_rules = s.sym_rules;
    sym_mstrat = s.sym_mstrat;
    sym_dtree = s.sym_dtree
  }


let rec find_at i = function
    |t::_ when i = 0 -> t
    |_::q -> find_at (i-1) q
    |[] -> failwith "index out of bounds"

let pprint_index i = if i < 0 then sprintf "?%i" (abs i) else sprintf "%i" i

let var_layer = function
  |LVari (_,i) -> i
  |_ -> failwith "not a var"

let print_list = fun acc s ->
  if acc = "" then begin if s < 0 then "?" ^ (string_of_int (-s)) else (string_of_int s) end
  else begin if s >= 0 then  acc ^ "," ^ (string_of_int s) else acc ^ "," ^ "?" ^ (string_of_int (-s)) end

let rec dlprint = function
    |LVari (v,i) -> sprintf "(Vari %s,%s)" (name_of v) (pprint_index i)
    |LType i -> sprintf "(Type %s)" (pprint_index i)
    |LKind i -> sprintf "(Kind %s)" (pprint_index i)
    |LProd (t,tb,i) -> let v,tt = unbind tb in sprintf "(Prod (%s,(%s %s,%s)), %s)" (dlprint t) (name_of(v)) (pprint_index (var_layer (unbox (box_var v)))) (dlprint tt) (pprint_index i)
    |LAbst (t,tb,i) ->  let v,tt = unbind tb in sprintf "(Abst (%s,(%s %s,%s)), %s)" (dlprint t) (name_of(v)) (pprint_index (var_layer (unbox (box_var v)))) (dlprint (tt)) (pprint_index i)
    |LAppl (t1,t2, i) -> sprintf "(Appl (%s,%s), %s)" (dlprint t1) (dlprint t2) (pprint_index i)
    |LSymb (s,i) -> sprintf "(%s [%s])" s.sym_name (List.fold_left (print_list) "" i)

let rec pprint = function
  |LVari  (v,i) -> sprintf "(%s,%s)" (name_of v) (pprint_index i)
  |LType i -> sprintf "TYPE %s" (pprint_index i)
  |LKind i -> sprintf "KIND %s" (pprint_index i)
  |LProd (t,tb,i) -> sprintf "((Π %s : %s . %s),%s)" (name_of (fst (unbind tb))) (pprint t) (pprint (snd (unbind (tb)))) (pprint_index i)
  |LAbst (t,tb,i) -> sprintf "((λ %s^%s : %s . %s),%s)" (name_of (fst (unbind tb))) (let vari = unbox (box_var (fst (unbind tb))) in let geti = function |LVari (_,i) -> i |_ -> failwith "not a var" in (pprint_index (geti vari))) (pprint t) (pprint (snd (unbind (tb)))) (pprint_index i)
  |LAppl (t1 ,t2, i) -> sprintf "((%s %s),%s)" (pprint t1) (pprint t2) (pprint_index i)
  |LSymb (s,i) -> sprintf "(%s,[%s])" s.sym_name (List.fold_left (print_list) "" i)

let labst : layered_term box -> ltbinder box -> int -> layered_term box = fun t b i -> box_apply2 (fun t b -> LAbst (t,b,i)) t b

let lvar : layered_term var -> layered_term box = fun x -> box_var x

let lapp : layered_term box -> layered_term box -> int -> layered_term box =  fun t u i -> box_apply2 (fun t u -> LAppl (t,u,i)) t u

let lprod : layered_term box -> ltbinder box -> int -> layered_term box = fun t b i -> box_apply2 (fun t b -> LProd (t,b,i)) t b

let ltype : int -> layered_term box = fun i -> box (LType i)

let lkind : int -> layered_term box = fun i -> box (LKind i)

let lsymb : lsym -> int list -> layered_term  box = fun s l -> box (LSymb (s,l))

let mkfree = fun i x -> LVari (x, i)

let renew i = i := 0

let index id ids = let o = List.assoc_opt id ids in match o with |Some i -> i |None -> dcr i;;

let arity : expr -> int = fun e ->
  let rec aux = fun e -> match e with
  |Fun (a,b) -> 1 + aux a + aux b
  |_ -> 0 in
aux e

let rec is_in_list elt = function
  |[] -> false
  |t::_ when t = elt -> true
  |_::q -> is_in_list elt q

let rec add_new l1 l2 = match l1 with
  |[] -> []
  |t::q -> if is_in_list t l2 then add_new q l2 else t::(add_new q l2)

let get_var_of_expr = fun e ->
  let layer_expr = e in
  let rec aux acc expr = match expr with
    |Fun (a,b) -> add_new (aux acc a) (aux acc b)
    |Var ev when not (is_in_list ev acc)-> ev::acc
    |Var _ -> acc
    |Zero -> acc
    |Succ _ -> acc
    |Add (a,b) -> add_new (aux acc a) (aux acc b) in
  let vars = aux [] layer_expr in
  vars

let new_layer_values : expr -> int list = fun e ->
  print_string ("erreur en dessous");
  let a = List.length (get_var_of_expr e) in
  let rec create_list a = match a with
    |0 -> []
    |_ -> (dcr i)::(create_list (a-1)) in
  create_list (a)

let rec lift_lt : layered_term -> layered_term  box = function
  |LVari (x,_) -> box_var x
  |LType i -> ltype i
  |LKind i -> lkind i
  |LAppl (t1,t2, i) -> lapp (lift_lt t1) (lift_lt t2) i
  |LProd (t1,t2,i) -> lprod (lift_lt t1) (box_binder lift_lt t2) i
  |LAbst (t1,t2,i) -> labst (lift_lt t1) (box_binder lift_lt t2) i
  |LSymb (s,i) -> lsymb s i

let rec term_to_layered_term mapping t layers_of_symbs = match t with
  |Vari x -> let x',i = List.assoc x  mapping in LVari (x', i)
  |Type -> LType (dcr i)
  |Kind -> LKind (dcr i)
  |Prod (t1,t2) ->
    let t1' = term_to_layered_term  mapping t1 layers_of_symbs in
    let u,v = unbind t2 in
    let u' = new_var (mkfree (dcr i)) (name_of u) in
    let v' = term_to_layered_term  ((u,(u',!i))::mapping) v layers_of_symbs in
    let t2' = unbox (bind_var u' (lift_lt v')) in
    LProd (t1', t2', (dcr i))
  |Abst (t1,t2) ->
    let t1' = term_to_layered_term  mapping t1 layers_of_symbs in
    let u,v = unbind t2 in
    let u' = new_var (mkfree (dcr i)) (name_of u) in
    let v' = term_to_layered_term  ((u,(u',!i))::mapping) v layers_of_symbs in
    let t2' = unbox (bind_var u' (lift_lt v')) in
    LAbst (t1', t2', (dcr i))
  |Appl (t1,t2) -> LAppl (term_to_layered_term   mapping t1 layers_of_symbs, term_to_layered_term   mapping t2 layers_of_symbs, (dcr i))
  |Symb s -> let layer = (List.assoc s.sym_name layers_of_symbs) in LSymb (sym_to_lsym s layer,new_layer_values layer)
  |_ -> failwith "pas marché"


let rec print_mapping = function
  |[] -> ""
  |t::q -> (sprintf "%s : %i ; " (name_of t) (uid_of t)) ^ (print_mapping q)

let rec in_list elt = function
  |[] -> false
  |t :: q -> if t = elt then true else in_list elt q

let rec replace m n l = match l with
  |[] -> failwith "not found"
  |t::q when t = m -> n::q
  |t::q -> t::(replace m n q)

let rec refine mapping m n t = match t with
  |LVari (x,i) when i = -m -> begin printf "voici la liste %s; " (print_mapping (List.map fst mapping)); printf "%s : %i " (name_of x) (uid_of x);  LVari (List.assoc x mapping,n) end
  |LType i when i = -m -> LType n
  |LKind i when i = -m -> LKind n
  |LProd (t1,t2,i) when i = -m -> LProd (t1,t2,n)
  |LProd (t1,t2,j) ->
    let t1' = refine mapping m n t1 in
    let x,t = unbind t2 in
    let i = var_layer (unbox (box_var x)) in
    if i = m then
      let x' = new_var (mkfree n) (name_of x) in
      let t' = refine ((x,x')::mapping) m n t in
      let t2' = unbox (bind_var x' (lift_lt t')) in
      LProd (t1',t2',j)
    else
      let t' = refine mapping m n t in
      let t2' = unbox (bind_var x (lift_lt t')) in
      LProd (t1',t2',j)
  |LAbst (t1,t2,i) when i = -m -> LAbst (t1,t2,n)
  |LAbst (t1,t2,j) ->
    let t1' = refine mapping m n t1 in
    let x,t = unbind t2 in
    let i = var_layer (unbox (box_var x)) in
    if i = -m then
      let x' = new_var (mkfree n) (name_of x) in
      let t' = refine ((x,x')::mapping) m n t in
      let t2' = unbox (bind_var x' (lift_lt t')) in
      LAbst (t1',t2',j)
    else
      let t' = refine mapping m n t in
      let t2' = unbox (bind_var x (lift_lt t')) in
      LAbst (t1',t2',j)
  |LAppl (t1,t2,i) when i = -m -> LAppl (t1,t2,n)
  |LAppl (t1,t2,i) -> LAppl (refine mapping m n t1, refine mapping m n t2, i)
  |LSymb (s,l) when in_list (-m) l -> LSymb (s, replace (-m) n l)
  |_ as t -> t

let layer = function
  |LVari (_,i) -> [i]
  |LType i -> [i]
  |LKind i -> [i]
  |LAppl (_,_,i) -> [i]
  |LAbst (_,_,i) -> [i]
  |LProd (_,_,i) -> [i]
  |LSymb (_,i) -> i

let get_layer t = let f = function [] -> failwith "get_layer : liste vide" |t::_ -> t in f (layer t)

let rec is_symb_application = function
  |LAppl (f,_,_) -> is_symb_application f
  |LSymb (_,_) -> true
  |_ -> false

let rec get_symb_application_name_layer = function
  |LAppl (f,_,_) -> get_symb_application_name_layer f
  |LSymb (s,l) -> s,l
  |_ -> failwith "not a symbol application"


(*On lui donne le nom d'un symbole et un terme d'application du symbole et il renvoit les arguments*)
let get_symbol_arguments : string -> layered_term -> layered_term list = fun name t ->
  let symb = try fst (get_symb_application_name_layer t) with _ -> failwith "no symbol" in
  if symb.sym_name = name then
    let rec aux = function
      |LAppl(f,x,_) -> x::(aux f)
      |LSymb _ -> []
      |_ -> failwith "chelou"
    in List.rev (aux t)
  else
    failwith "not the symbol i was looking for"

let rec less argslayer symblayer = match symblayer with
  |[] -> true
  |t::q -> if List.hd argslayer <= t then less (List.tl argslayer) q else false

let rec is_in_list elt = function
  |[] -> false
  |t::_ when t = elt -> true
  |_::q -> is_in_list elt q

let rec add_new l1 l2 = match l1 with
  |[] -> []
  |t::q -> if is_in_list t l2 then add_new q l2 else t::(add_new q l2)

let get_var_of_symb_layer = fun symb ->
  let layer_expr = symb.sym_layer in
  let rec aux acc expr = match expr with
    |Fun (a,b) -> add_new (aux acc a) (aux acc b)
    |Var ev when not (is_in_list ev acc)-> ev::acc
    |Var _ -> acc
    |Zero -> acc
    |Succ _ -> acc
    |Add (a,b) -> add_new (aux acc a) (aux acc b) in
  let vars = aux [] layer_expr in
  vars

let get_symb_layer = fun symb layer ->
  let layer_expr = symb.sym_layer in
  let vars = get_var_of_symb_layer symb in
  let rec assoc_list = fun vars layer ->
    match vars with
    |[] -> []
    |t::q -> (t,List.hd layer)::(assoc_list q (List.tl layer)) in
  let assoc_list = assoc_list vars layer in
  let rec layer_to_list = function
    |Fun(a,b) -> (layer_to_list a)@[b]
    |_ as t -> [t] in
  let layer_list = layer_to_list layer_expr in
  let rec compute_partial_layer = fun assoc_list expr ->
    match expr with
    |Var ev -> List.assoc ev assoc_list
    |Succ a -> 1 + (compute_partial_layer assoc_list a)
    |Zero -> 0
    |Add (a,b) -> compute_partial_layer assoc_list a + compute_partial_layer assoc_list b
    |Fun _ -> failwith "not a normal form" in
  let layer_list = List.map (compute_partial_layer assoc_list) layer_list in
  layer_list

let rec check_layer t = match t with
  |LAppl (f,x,lapp) as t when not (is_symb_application t) -> let lf,lx = get_layer f, get_layer x in if lapp = 1 then lf <= 1 && lx <= lf else lf = lapp && lx <= lapp && check_layer f && check_layer x
  |LAppl (_,_,lapp) as t -> let symb =  fst (get_symb_application_name_layer t) in
    let args = get_symbol_arguments (symb.sym_name) t in
    let args_layer = List.map (get_layer) args in let args_layer = List.rev(lapp::(List.rev args_layer)) in
    let symb_layer = get_symb_layer symb (snd (get_symb_application_name_layer t)) in
    let well_layered_argument = List.map (check_layer) args in
    let rec aux = function
      |[] -> true
      |t::q -> if t then aux q else false in
    less args_layer symb_layer && List.hd(List.rev symb_layer) = lapp && aux well_layered_argument
  |LAbst (ty,b,labst) -> let _,u = unbind b in let lu, lty = get_layer u, get_layer ty in labst > 0 && lty <= labst && lu <= labst && check_layer u && check_layer ty
  |LProd (ty,b,lprod) -> let _,u = unbind b in let lu, lty = get_layer u, get_layer ty in lprod > 0 && lty = lprod && lu <= lprod  && check_layer u && check_layer ty
  |_ -> true
