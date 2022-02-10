
module MenhirBasics = struct
  
  exception Error
  
  let _eRR : exn =
    Error
  
  type token = DkLexer.token
  
end

include MenhirBasics

type _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  _menhir_token: token;
  mutable _menhir_error: bool
}

and _menhir_state = 
  | MenhirState131
  | MenhirState129
  | MenhirState126
  | MenhirState122
  | MenhirState119
  | MenhirState116
  | MenhirState115
  | MenhirState111
  | MenhirState109
  | MenhirState106
  | MenhirState103
  | MenhirState101
  | MenhirState100
  | MenhirState96
  | MenhirState93
  | MenhirState90
  | MenhirState87
  | MenhirState84
  | MenhirState80
  | MenhirState77
  | MenhirState74
  | MenhirState73
  | MenhirState72
  | MenhirState68
  | MenhirState65
  | MenhirState62
  | MenhirState53
  | MenhirState49
  | MenhirState46
  | MenhirState44
  | MenhirState38
  | MenhirState36
  | MenhirState31
  | MenhirState27
  | MenhirState25
  | MenhirState23
  | MenhirState21
  | MenhirState20
  | MenhirState19
  | MenhirState18
  | MenhirState17
  | MenhirState16
  | MenhirState14
  | MenhirState13
  | MenhirState12
  | MenhirState7
  | MenhirState6
  | MenhirState5
  | MenhirState3
  | MenhirState0

# 1 "src/parsing/dkParser.mly"
  

open! Lplib
open Timed
open Common
open Pos
open Syntax
open DkLexer
open Error
open Core

(** [get_args t] decomposes the parser level term [t] into a spine [(h,args)],
    when [h] is the term at the head of the application and [args] is the list
    of all its arguments.  The arguments are stored together with the position
    of the corresponding application node in the source code. Note that [h] is
    guaranteed not to be a [P_Appl] node. Term constructors with no equivalent
    in the legacy syntax (like binary symbol applications) are not handled. *)
let get_args : p_term -> p_term * (Pos.popt * p_term) list = fun t ->
  let rec get_args acc t =
    match t.elt with
    | P_Appl(u,v) -> get_args ((t.pos,v)::acc) u
    | _           -> (t, acc)
  in get_args [] t

(** [add_args t args] builds the application of the term [t] to the  arguments
    [args]. When [args] is empty, the returned value is exactly [t]. Note that
    this function is the inverse of [get_args] (in some sense). *)
let add_args : p_term -> (Pos.popt * p_term) list -> p_term =
  List.fold_left (fun t (p,u) -> Pos.make p (P_Appl(t,u)))

(** Representation of a reduction rule, with its context. *)
type old_p_rule = ((strloc * p_term option) list * p_term * p_term) Pos.loc

(** [translate_old_rule r] transforms the legacy representation of a rule into
    the new representation. This function will be removed soon. *)
let translate_old_rule : old_p_rule -> p_rule = fun r ->
  let (ctx, lhs, rhs) = r.elt in
  (* Check for (deprecated) annotations in the context. *)
  let get_var (x,ao) =
    let fn a = wrn a.pos "Ignored type annotation." in
    (if !Console.verbose > 1 then Option.iter fn ao); x
  in
  let ctx = List.map get_var ctx in
  let is_pat_var env x =
    not (List.mem x env) && List.exists (fun y -> y.elt = x) ctx
  in
  (* Find the maximum number of arguments a variable is applied to. *)
  let arity = Hashtbl.create 7 in
  let rec compute_arities env t =
    let (h, args) = get_args t in
    let nb_args = List.length args in
    begin
      match h.elt with
      | P_Appl(_,_)       -> assert false (* Cannot happen. *)
      | P_Iden(x,_)       ->
          let (p,x) = x.elt in
          if p = [] && is_pat_var env x then
            begin
              try
                let n = Hashtbl.find arity x in
                if nb_args > n then Hashtbl.replace arity x nb_args
              with Not_found -> Hashtbl.add arity x nb_args
            end
      | P_Wild            -> ()
      | P_Type            -> fatal h.pos "Type in legacy pattern."
      | P_Prod(_,_)       -> fatal h.pos "Product in legacy pattern."
      | P_Abst(xs,t)      ->
          begin
            match xs with
            | [(_       ,Some(a),_)] ->
                fatal a.pos "Annotation in legacy pattern."
            | [([Some x],None   ,_)] ->
                compute_arities (x.elt::env) t
            | [([None  ],None   ,_)] ->
                compute_arities env t
            | _                      -> assert false
          end
      | P_Arro(_,_)       -> fatal h.pos "Implication in legacy pattern."
      | P_LLet(_,_,_,_,_) -> fatal h.pos "Let expression in legacy rule."
      | P_Meta(_,_)       -> assert false
      | P_Patt(_,_)       -> assert false
      | P_NLit(_)         -> assert false
      | P_Wrap(_)         -> assert false
      | P_Expl(_)         -> assert false
    end;
    List.iter (fun (_,t) -> compute_arities env t) args
  in
  compute_arities [] lhs;
  (* Check that all context variables occur in the LHS. *)
  let check_here x =
    try ignore (Hashtbl.find arity x.elt) with Not_found ->
      fatal x.pos "Variable [%s] does not occur in the LHS." x.elt
  in
  List.iter check_here ctx;
  (* Actually process the LHS and RHS. *)
  let rec build env t =
    let (h, lts) = get_args t in
    match h.elt with
    | P_Iden({elt = ([],x); _}, _) when is_pat_var env x ->
        let lts = List.map (fun (p, t) -> (p, build env t)) lts in
        let max = try Hashtbl.find arity x with Not_found -> assert false in
        let k = List.length lts in
        (* Number of η-expansions required. *)
        let nb_exp = if k >= max then 0 else max - k in
        let p = t.pos in
        if nb_exp = 0 then
          (* No η-expansion required (enough arguments). *)
          let (lts1, lts2) = List.cut lts max in
          let ts1 = Array.of_list (List.map snd lts1) in
          let patt = Pos.make p (P_Patt(Some(Pos.make h.pos x), Some ts1)) in
          add_args patt lts2
        else
          (* We need to η-expense (not enough arguments). *)
          let ts = Array.of_list (List.map snd lts) in
          (* Create fresh variables. *)
          let ctx = List.map (fun x -> x.elt) ctx in
          (* Function to create fresh variable names. *)
          let new_var_name : unit -> string =
            let counter = ref (-1) in
            fun () ->
              incr counter;
              while List.mem (Printf.sprintf "v%i" !counter) ctx do
                incr counter
              done;
              Printf.sprintf "v%i" !counter
          in
          let vars = Array.init nb_exp (fun _ -> new_var_name ()) in
          (* Build the pattern. *)
          let fn x = Pos.none (P_Iden(Pos.none ([],x), false)) in
          let args = Array.append ts (Array.map fn vars) in
          let patt = Pos.make p (P_Patt(Some(Pos.make h.pos x), Some args)) in
          (* Build the abstraction. *)
          let xs = Array.map (fun x -> Some(Pos.none x)) vars in
          Pos.make p (P_Abst([Array.to_list xs, None, false], patt))
    | P_Wild when lts = [] && env = []                   -> t
    | P_Wild                                             ->
        let lts = List.map (fun (_, t) -> build env t) lts in
        Pos.make t.pos (P_Patt(None, Some (Array.of_list lts)))
    | _                                                  ->
    match t.elt with
    | P_Iden(_)
    | P_Type
    | P_Wild            -> t
    | P_Prod(xs,b)      ->
        let (x,a) =
          match xs with
          | [([Some x],Some(a),_)] -> (x, build env a)
          | _                      -> assert false (* Unreachable. *)
        in
        let b = build (x.elt::env) b in
        Pos.make t.pos (P_Prod([([Some x],Some(a),false)], b))
    | P_Arro(a,b)       -> Pos.make t.pos (P_Arro(build env a, build env b))
    | P_Abst(xs,u)      ->
        let (x,a) =
          match xs with
          | [([x],ao,_)] -> (x, Option.map (build env) ao)
          | _            -> assert false (* Unreachable. *)
        in
        let u =
          match x with
          | Some(x) -> build (x.elt::env) u
          | None    -> build env u
        in
        Pos.make t.pos (P_Abst([([x],a,false)], u))
    | P_Appl(t1,t2)     -> Pos.make t.pos (P_Appl(build env t1, build env t2))
    | P_Meta(_,_)       -> fatal t.pos "Invalid legacy rule syntax."
    | P_Patt(_,_)       -> fatal h.pos "Pattern in legacy rule."
    | P_LLet(_,_,_,_,_) -> fatal h.pos "Let expression in legacy rule."
    | P_NLit(_)         -> fatal h.pos "Nat literal in legacy rule."
    | P_Wrap(_)         -> fatal h.pos "Wrapping constructor in legacy rule."
    | P_Expl(_)         -> fatal h.pos "Explicit argument in legacy rule."
  in
  (* NOTE the computation order is important for setting arities properly. *)
  let lhs = build [] lhs in
  let rhs = build [] rhs in
  Pos.make r.pos (lhs, rhs)

let build_strat : Pos.pos -> string -> string option -> Eval.strat =
    fun loc s1 s2o ->
  try
    let config steps strategy =
      Eval.{strategy; steps=Option.map int_of_string steps}
    in
    match (s1, s2o) with
    | ("SNF" , io         ) -> config io        SNF
    | ("HNF" , io         ) -> config io        HNF
    | ("WHNF", io         ) -> config io        WHNF
    | (i     , Some "SNF" ) -> config (Some(i)) SNF
    | (i     , Some "HNF" ) -> config (Some(i)) HNF
    | (i     , Some "WHNF") -> config (Some(i)) WHNF
    | (i     , None       ) -> config (Some(i)) NONE
    | (_     , _          ) -> raise Exit (* captured below *)
  with _ -> fatal (Some(loc)) "Invalid strategy."


# 271 "src/parsing/dkParser.ml"

let rec _menhir_goto_nonempty_list_param_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_nonempty_list_param_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState106 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv523 * _menhir_state * 'tv_param) * _menhir_state * 'tv_nonempty_list_param_) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv521 * _menhir_state * 'tv_param) * _menhir_state * 'tv_nonempty_list_param_) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (x : 'tv_param)), _, (xs : 'tv_nonempty_list_param_)) = _menhir_stack in
        let _v : 'tv_nonempty_list_param_ = 
# 223 "<standard.mly>"
    ( x :: xs )
# 286 "src/parsing/dkParser.ml"
         in
        _menhir_goto_nonempty_list_param_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv522)) : 'freshtv524)
    | MenhirState100 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv529 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 294 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv525 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 304 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | DkLexer.LEFTPAR ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.QID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState109 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.TYPE ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UID _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState109 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UNDERSCORE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState109) : 'freshtv526)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv527 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 330 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv528)) : 'freshtv530)
    | MenhirState115 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv537 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 339 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv531 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 349 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | DkLexer.LEFTPAR ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.QID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState129 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.TYPE ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UID _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState129 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UNDERSCORE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState129) : 'freshtv532)
        | DkLexer.DEF ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv533 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 373 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | DkLexer.LEFTPAR ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState126 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.QID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState126 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.TYPE ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState126 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UID _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState126 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UNDERSCORE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState126 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState126) : 'freshtv534)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv535 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 399 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv536)) : 'freshtv538)
    | _ ->
        _menhir_fail ()

and _menhir_goto_nonempty_list_rule_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_nonempty_list_rule_ -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState80 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv511 * _menhir_state * 'tv_rule * Lexing.position) * _menhir_state * 'tv_nonempty_list_rule_ * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv509 * _menhir_state * 'tv_rule * Lexing.position) * _menhir_state * 'tv_nonempty_list_rule_ * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (x : 'tv_rule), _startpos_x_), _, (xs : 'tv_nonempty_list_rule_), _startpos_xs_) = _menhir_stack in
        let _startpos = _startpos_x_ in
        let _v : 'tv_nonempty_list_rule_ = 
# 223 "<standard.mly>"
    ( x :: xs )
# 420 "src/parsing/dkParser.ml"
         in
        _menhir_goto_nonempty_list_rule_ _menhir_env _menhir_stack _menhir_s _v _startpos) : 'freshtv510)) : 'freshtv512)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv519 * _menhir_state * 'tv_nonempty_list_rule_ * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv515 * _menhir_state * 'tv_nonempty_list_rule_ * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv513 * _menhir_state * 'tv_nonempty_list_rule_ * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__2_ : Lexing.position) = _endpos in
            ((let (_menhir_stack, _menhir_s, (rs : 'tv_nonempty_list_rule_), _startpos_rs_) = _menhir_stack in
            let _v : (
# 237 "src/parsing/dkParser.mly"
      (Syntax.p_command)
# 440 "src/parsing/dkParser.ml"
            ) = let _endpos = _endpos__2_ in
            let _symbolstartpos = _startpos_rs_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 345 "src/parsing/dkParser.mly"
                 (
      make_pos _sloc (P_rules(List.map translate_old_rule rs))
    )
# 449 "src/parsing/dkParser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv514)) : 'freshtv516)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv517 * _menhir_state * 'tv_nonempty_list_rule_ * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv518)) : 'freshtv520)
    | _ ->
        _menhir_fail ()

and _menhir_run25 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_term * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | DkLexer.LEFTPAR ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState25 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DkLexer.QID _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState25 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DkLexer.TYPE ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState25 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DkLexer.UID _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState25 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DkLexer.UNDERSCORE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState25 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState25

and _menhir_goto_list_param_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_list_param_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState93 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv501 * _menhir_state * 'tv_param) * _menhir_state * 'tv_list_param_) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv499 * _menhir_state * 'tv_param) * _menhir_state * 'tv_list_param_) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (x : 'tv_param)), _, (xs : 'tv_list_param_)) = _menhir_stack in
        let _v : 'tv_list_param_ = 
# 213 "<standard.mly>"
    ( x :: xs )
# 495 "src/parsing/dkParser.ml"
         in
        _menhir_goto_list_param_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv500)) : 'freshtv502)
    | MenhirState87 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv507 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 503 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state * 'tv_list_param_) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv503 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 513 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_list_param_) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | DkLexer.LEFTPAR ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState96 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.QID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState96 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.TYPE ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState96 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UID _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState96 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UNDERSCORE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState96 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState96) : 'freshtv504)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv505 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 539 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_list_param_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv506)) : 'freshtv508)
    | _ ->
        _menhir_fail ()

and _menhir_goto_separated_nonempty_list_COMMA_context_item_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_separated_nonempty_list_COMMA_context_item_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState3 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv493) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_separated_nonempty_list_COMMA_context_item_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv491) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let ((x : 'tv_separated_nonempty_list_COMMA_context_item_) : 'tv_separated_nonempty_list_COMMA_context_item_) = _v in
        ((let _v : 'tv_loption_separated_nonempty_list_COMMA_context_item__ = 
# 144 "<standard.mly>"
    ( x )
# 561 "src/parsing/dkParser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_COMMA_context_item__ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv492)) : 'freshtv494)
    | MenhirState49 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv497 * _menhir_state * 'tv_context_item)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_separated_nonempty_list_COMMA_context_item_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv495 * _menhir_state * 'tv_context_item)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((xs : 'tv_separated_nonempty_list_COMMA_context_item_) : 'tv_separated_nonempty_list_COMMA_context_item_) = _v in
        ((let (_menhir_stack, _menhir_s, (x : 'tv_context_item)) = _menhir_stack in
        let _v : 'tv_separated_nonempty_list_COMMA_context_item_ = 
# 243 "<standard.mly>"
    ( x :: xs )
# 577 "src/parsing/dkParser.ml"
         in
        _menhir_goto_separated_nonempty_list_COMMA_context_item_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv496)) : 'freshtv498)
    | _ ->
        _menhir_fail ()

and _menhir_goto_term : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_term -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState23 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv285 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 592 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) * Lexing.position * _menhir_state)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.COMMA | DkLexer.DEF | DkLexer.DOT | DkLexer.LEFTSQU | DkLexer.LONGARROW | DkLexer.RIGHTPAR | DkLexer.RIGHTSQU ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv281 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 604 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) * Lexing.position * _menhir_state)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((((((_menhir_stack, _menhir_s, _startpos__1_), _endpos_x_, _, (x : (
# 231 "src/parsing/dkParser.mly"
       (string)
# 609 "src/parsing/dkParser.ml"
            )), _startpos_x_), _), _endpos_a_, _, (a : 'tv_aterm), _startpos_a_), _endpos__5_, _), _endpos_b_, _, (b : 'tv_term), _startpos_b_) = _menhir_stack in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos_b_ in
            let _v : 'tv_term = let _endpos = _endpos_b_ in
            let _symbolstartpos = _startpos__1_ in
            let _loc_x_ = (_startpos_x_, _endpos_x_) in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 422 "src/parsing/dkParser.mly"
                                                      (
      let x = make_pos _loc_x_ x in
      make_pos _sloc (P_Prod([([Some x], Some(a), false)], b))
    )
# 623 "src/parsing/dkParser.ml"
             in
            _menhir_goto_term _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv282)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv283 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 633 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) * Lexing.position * _menhir_state)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv284)) : 'freshtv286)
    | MenhirState25 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv291 * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.COMMA | DkLexer.DEF | DkLexer.DOT | DkLexer.LEFTSQU | DkLexer.LONGARROW | DkLexer.RIGHTPAR | DkLexer.RIGHTSQU ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv287 * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _endpos_a_, _menhir_s, (a : 'tv_term), _startpos_a_), _endpos_b_, _, (b : 'tv_term), _startpos_b_) = _menhir_stack in
            let _startpos = _startpos_a_ in
            let _endpos = _endpos_b_ in
            let _v : 'tv_term = let _endpos = _endpos_b_ in
            let _symbolstartpos = _startpos_a_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 426 "src/parsing/dkParser.mly"
                        (
      make_pos _sloc (P_Arro(a, b))
    )
# 659 "src/parsing/dkParser.ml"
             in
            _menhir_goto_term _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv288)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv289 * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv290)) : 'freshtv292)
    | MenhirState31 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv297 * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 674 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state * 'tv_option_type_annot_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.COMMA | DkLexer.DEF | DkLexer.DOT | DkLexer.LEFTSQU | DkLexer.LONGARROW | DkLexer.RIGHTPAR | DkLexer.RIGHTSQU ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv293 * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 686 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_option_type_annot_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _endpos_x_, _menhir_s, (x : (
# 231 "src/parsing/dkParser.mly"
       (string)
# 691 "src/parsing/dkParser.ml"
            )), _startpos_x_), _, (a : 'tv_option_type_annot_)), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
            let _startpos = _startpos_x_ in
            let _endpos = _endpos_t_ in
            let _v : 'tv_term = let _endpos = _endpos_t_ in
            let _symbolstartpos = _startpos_x_ in
            let _loc_x_ = (_startpos_x_, _endpos_x_) in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 432 "src/parsing/dkParser.mly"
                                               (
      let x = make_pos _loc_x_ x in
      make_pos _sloc (P_Abst([([Some x], a, false)], t))
    )
# 705 "src/parsing/dkParser.ml"
             in
            _menhir_goto_term _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv294)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv295 * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 715 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_option_type_annot_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv296)) : 'freshtv298)
    | MenhirState12 | MenhirState18 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv305 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.RIGHTPAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv301 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv299 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__3_ : Lexing.position) = _endpos in
            ((let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : 'tv_sterm = 
# 407 "src/parsing/dkParser.mly"
                            ( t )
# 741 "src/parsing/dkParser.ml"
             in
            _menhir_goto_sterm _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv300)) : 'freshtv302)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv303 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv304)) : 'freshtv306)
    | MenhirState17 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv311 * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 756 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.COMMA | DkLexer.DEF | DkLexer.DOT | DkLexer.LEFTSQU | DkLexer.LONGARROW | DkLexer.RIGHTPAR | DkLexer.RIGHTSQU ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv307 * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 768 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (((((_menhir_stack, _endpos_x_, _menhir_s, (x : (
# 231 "src/parsing/dkParser.mly"
       (string)
# 773 "src/parsing/dkParser.ml"
            )), _startpos_x_), _), _endpos_a_, _, (a : 'tv_aterm), _startpos_a_), _), _endpos_b_, _, (b : 'tv_term), _startpos_b_) = _menhir_stack in
            let _startpos = _startpos_x_ in
            let _endpos = _endpos_b_ in
            let _v : 'tv_term = let _endpos = _endpos_b_ in
            let _symbolstartpos = _startpos_x_ in
            let _loc_x_ = (_startpos_x_, _endpos_x_) in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 418 "src/parsing/dkParser.mly"
                                     (
      let x = make_pos _loc_x_ x in
      make_pos _sloc (P_Prod([([Some x], Some(a), false)], b))
    )
# 787 "src/parsing/dkParser.ml"
             in
            _menhir_goto_term _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv308)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv309 * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 797 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv310)) : 'freshtv312)
    | MenhirState38 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv317 * Lexing.position * _menhir_state * Lexing.position) * _menhir_state * 'tv_option_type_annot_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.COMMA | DkLexer.DEF | DkLexer.DOT | DkLexer.LEFTSQU | DkLexer.LONGARROW | DkLexer.RIGHTPAR | DkLexer.RIGHTSQU ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv313 * Lexing.position * _menhir_state * Lexing.position) * _menhir_state * 'tv_option_type_annot_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _endpos__1_, _menhir_s, _startpos__1_), _, (a : 'tv_option_type_annot_)), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos_t_ in
            let _v : 'tv_term = let _endpos = _endpos_t_ in
            let _symbolstartpos = _startpos__1_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 429 "src/parsing/dkParser.mly"
                                                    (
      make_pos _sloc (P_Abst([([None], a, false)], t))
    )
# 823 "src/parsing/dkParser.ml"
             in
            _menhir_goto_term _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv314)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv315 * Lexing.position * _menhir_state * Lexing.position) * _menhir_state * 'tv_option_type_annot_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv316)) : 'freshtv318)
    | MenhirState5 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv323) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.COMMA | DkLexer.RIGHTSQU ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv319) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _endpos_a_, _, (a : 'tv_term), _startpos_a_) = _menhir_stack in
            let _v : 'tv_option___anonymous_0_ = let x = 
# 395 "src/parsing/dkParser.mly"
                                 ( a )
# 848 "src/parsing/dkParser.ml"
             in
            
# 116 "<standard.mly>"
    ( Some x )
# 853 "src/parsing/dkParser.ml"
             in
            _menhir_goto_option___anonymous_0_ _menhir_env _menhir_stack _v) : 'freshtv320)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv321) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv322)) : 'freshtv324)
    | MenhirState44 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv329 * _menhir_state * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_COMMA_context_item__) * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.LONGARROW ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv325 * _menhir_state * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_COMMA_context_item__) * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | DkLexer.LEFTPAR ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.QID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState46 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.TYPE ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState46 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UID _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState46 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UNDERSCORE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState46 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState46) : 'freshtv326)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv327 * _menhir_state * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_COMMA_context_item__) * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv328)) : 'freshtv330)
    | MenhirState46 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv341 * _menhir_state * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_COMMA_context_item__) * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.DOT | DkLexer.LEFTSQU ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((('freshtv337 * _menhir_state * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_COMMA_context_item__) * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (((((_menhir_stack, _menhir_s, _startpos__1_), _, (xs : 'tv_loption_separated_nonempty_list_COMMA_context_item__)), _endpos__3_), _endpos_l_, _, (l : 'tv_term), _startpos_l_), _endpos_r_, _, (r : 'tv_term), _startpos_r_) = _menhir_stack in
            let _startpos = _startpos__1_ in
            let _v : 'tv_rule = let c = 
# 232 "<standard.mly>"
    ( xs )
# 914 "src/parsing/dkParser.ml"
             in
            let _endpos = _endpos_r_ in
            let _symbolstartpos = _startpos__1_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 400 "src/parsing/dkParser.mly"
    ( make_pos _sloc (c, l, r) )
# 922 "src/parsing/dkParser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv335) = _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_rule) = _v in
            let (_startpos : Lexing.position) = _startpos in
            ((let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos) in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv333 * _menhir_state * 'tv_rule * Lexing.position) = Obj.magic _menhir_stack in
            ((assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | DkLexer.LEFTSQU ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.DOT ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv331 * _menhir_state * 'tv_rule * Lexing.position) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, (x : 'tv_rule), _startpos_x_) = _menhir_stack in
                let _startpos = _startpos_x_ in
                let _v : 'tv_nonempty_list_rule_ = 
# 221 "<standard.mly>"
    ( [ x ] )
# 945 "src/parsing/dkParser.ml"
                 in
                _menhir_goto_nonempty_list_rule_ _menhir_env _menhir_stack _menhir_s _v _startpos) : 'freshtv332)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState80) : 'freshtv334)) : 'freshtv336)) : 'freshtv338)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((('freshtv339 * _menhir_state * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_COMMA_context_item__) * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv340)) : 'freshtv342)
    | MenhirState53 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv349 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv345 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv343 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__3_ : Lexing.position) = _endpos in
            ((let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
            let _v : (
# 237 "src/parsing/dkParser.mly"
      (Syntax.p_command)
# 978 "src/parsing/dkParser.ml"
            ) = let _endpos = _endpos__3_ in
            let _symbolstartpos = _startpos__1_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 358 "src/parsing/dkParser.mly"
                     (
      let c = Eval.{strategy = NONE; steps = None} in
      let q = make_pos _sloc (P_query_infer(t, c)) in
      make_pos _sloc (P_query q)
    )
# 989 "src/parsing/dkParser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv344)) : 'freshtv346)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv347 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv348)) : 'freshtv350)
    | MenhirState62 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv357 * _menhir_state * Lexing.position) * _menhir_state * 'tv_eval_config) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv353 * _menhir_state * Lexing.position) * _menhir_state * 'tv_eval_config) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv351 * _menhir_state * Lexing.position) * _menhir_state * 'tv_eval_config) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__4_ : Lexing.position) = _endpos in
            ((let (((_menhir_stack, _menhir_s, _startpos__1_), _, (c : 'tv_eval_config)), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
            let _v : (
# 237 "src/parsing/dkParser.mly"
      (Syntax.p_command)
# 1018 "src/parsing/dkParser.ml"
            ) = let _endpos = _endpos__4_ in
            let _symbolstartpos = _startpos__1_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 363 "src/parsing/dkParser.mly"
                                   (
      let q = make_pos _sloc (P_query_infer(t, c)) in
      make_pos _sloc (P_query q)
    )
# 1028 "src/parsing/dkParser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv352)) : 'freshtv354)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv355 * _menhir_state * Lexing.position) * _menhir_state * 'tv_eval_config) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv356)) : 'freshtv358)
    | MenhirState65 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv365 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv361 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv359 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__3_ : Lexing.position) = _endpos in
            ((let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
            let _v : (
# 237 "src/parsing/dkParser.mly"
      (Syntax.p_command)
# 1057 "src/parsing/dkParser.ml"
            ) = let _endpos = _endpos__3_ in
            let _symbolstartpos = _startpos__1_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 348 "src/parsing/dkParser.mly"
                    (
      let c = Eval.{strategy = SNF; steps = None} in
      let q = make_pos _sloc (P_query_normalize(t,c)) in
      make_pos _sloc (P_query q)
    )
# 1068 "src/parsing/dkParser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv360)) : 'freshtv362)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv363 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv364)) : 'freshtv366)
    | MenhirState68 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv373 * _menhir_state * Lexing.position) * _menhir_state * 'tv_eval_config) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv369 * _menhir_state * Lexing.position) * _menhir_state * 'tv_eval_config) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv367 * _menhir_state * Lexing.position) * _menhir_state * 'tv_eval_config) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__4_ : Lexing.position) = _endpos in
            ((let (((_menhir_stack, _menhir_s, _startpos__1_), _, (c : 'tv_eval_config)), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
            let _v : (
# 237 "src/parsing/dkParser.mly"
      (Syntax.p_command)
# 1097 "src/parsing/dkParser.ml"
            ) = let _endpos = _endpos__4_ in
            let _symbolstartpos = _startpos__1_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 353 "src/parsing/dkParser.mly"
                                  (
      let c = if c.strategy=NONE then {c with strategy=SNF} else c in
      let q = make_pos _sloc (P_query_normalize(t, c)) in
      make_pos _sloc (P_query q)
    )
# 1108 "src/parsing/dkParser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv368)) : 'freshtv370)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv371 * _menhir_state * Lexing.position) * _menhir_state * 'tv_eval_config) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv372)) : 'freshtv374)
    | MenhirState74 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv381 * _menhir_state * (
# 203 "src/parsing/dkParser.mly"
       (bool)
# 1123 "src/parsing/dkParser.ml"
        ) * Lexing.position) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv377 * _menhir_state * (
# 203 "src/parsing/dkParser.mly"
       (bool)
# 1135 "src/parsing/dkParser.ml"
            ) * Lexing.position) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv375 * _menhir_state * (
# 203 "src/parsing/dkParser.mly"
       (bool)
# 1142 "src/parsing/dkParser.ml"
            ) * Lexing.position) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__5_ : Lexing.position) = _endpos in
            ((let ((((_menhir_stack, _menhir_s, (mf : (
# 203 "src/parsing/dkParser.mly"
       (bool)
# 1148 "src/parsing/dkParser.ml"
            )), _startpos_mf_), _endpos_t_, _, (t : 'tv_aterm), _startpos_t_), _), _endpos_u_, _, (u : 'tv_term), _startpos_u_) = _menhir_stack in
            let _v : (
# 237 "src/parsing/dkParser.mly"
      (Syntax.p_command)
# 1153 "src/parsing/dkParser.ml"
            ) = let _endpos = _endpos__5_ in
            let _symbolstartpos = _startpos_mf_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 371 "src/parsing/dkParser.mly"
                                       (
      let q = make_pos _sloc (P_query_assert(mf, P_assert_conv(t,u))) in
      make_pos _sloc (P_query q)
    )
# 1163 "src/parsing/dkParser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv376)) : 'freshtv378)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv379 * _menhir_state * (
# 203 "src/parsing/dkParser.mly"
       (bool)
# 1173 "src/parsing/dkParser.ml"
            ) * Lexing.position) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv380)) : 'freshtv382)
    | MenhirState77 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv389 * _menhir_state * (
# 203 "src/parsing/dkParser.mly"
       (bool)
# 1182 "src/parsing/dkParser.ml"
        ) * Lexing.position) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv385 * _menhir_state * (
# 203 "src/parsing/dkParser.mly"
       (bool)
# 1194 "src/parsing/dkParser.ml"
            ) * Lexing.position) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv383 * _menhir_state * (
# 203 "src/parsing/dkParser.mly"
       (bool)
# 1201 "src/parsing/dkParser.ml"
            ) * Lexing.position) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__5_ : Lexing.position) = _endpos in
            ((let ((((_menhir_stack, _menhir_s, (mf : (
# 203 "src/parsing/dkParser.mly"
       (bool)
# 1207 "src/parsing/dkParser.ml"
            )), _startpos_mf_), _endpos_t_, _, (t : 'tv_aterm), _startpos_t_), _), _endpos_a_, _, (a : 'tv_term), _startpos_a_) = _menhir_stack in
            let _v : (
# 237 "src/parsing/dkParser.mly"
      (Syntax.p_command)
# 1212 "src/parsing/dkParser.ml"
            ) = let _endpos = _endpos__5_ in
            let _symbolstartpos = _startpos_mf_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 367 "src/parsing/dkParser.mly"
                                       (
      let q = make_pos _sloc (P_query_assert(mf, P_assert_typing(t,a))) in
      make_pos _sloc (P_query q)
    )
# 1222 "src/parsing/dkParser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv384)) : 'freshtv386)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv387 * _menhir_state * (
# 203 "src/parsing/dkParser.mly"
       (bool)
# 1232 "src/parsing/dkParser.ml"
            ) * Lexing.position) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv388)) : 'freshtv390)
    | MenhirState90 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv405 * _menhir_state * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1241 "src/parsing/dkParser.ml"
        ) * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.RIGHTPAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv401 * _menhir_state * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1253 "src/parsing/dkParser.ml"
            ) * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv399 * _menhir_state * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1261 "src/parsing/dkParser.ml"
            ) * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__5_ : Lexing.position) = _endpos in
            ((let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos_id_, (id : (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1267 "src/parsing/dkParser.ml"
            )), _startpos_id_), _endpos_te_, _, (te : 'tv_term), _startpos_te_) = _menhir_stack in
            let _v : 'tv_param = let _loc_id_ = (_startpos_id_, _endpos_id_) in
            
# 388 "src/parsing/dkParser.mly"
    ( ([Some (make_pos _loc_id_ id)], Some(te), false) )
# 1273 "src/parsing/dkParser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv397) = _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_param) = _v in
            ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            match _menhir_s with
            | MenhirState93 | MenhirState87 ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv391 * _menhir_state * 'tv_param) = Obj.magic _menhir_stack in
                ((assert (not _menhir_env._menhir_error);
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | DkLexer.LEFTPAR ->
                    _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | DkLexer.COLON ->
                    _menhir_reduce25 _menhir_env (Obj.magic _menhir_stack) MenhirState93
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState93) : 'freshtv392)
            | MenhirState115 | MenhirState106 | MenhirState100 ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv395 * _menhir_state * 'tv_param) = Obj.magic _menhir_stack in
                ((assert (not _menhir_env._menhir_error);
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | DkLexer.LEFTPAR ->
                    _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState106 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | DkLexer.COLON | DkLexer.DEF ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : 'freshtv393 * _menhir_state * 'tv_param) = Obj.magic _menhir_stack in
                    ((let (_menhir_stack, _menhir_s, (x : 'tv_param)) = _menhir_stack in
                    let _v : 'tv_nonempty_list_param_ = 
# 221 "<standard.mly>"
    ( [ x ] )
# 1310 "src/parsing/dkParser.ml"
                     in
                    _menhir_goto_nonempty_list_param_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv394)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState106) : 'freshtv396)
            | _ ->
                _menhir_fail ()) : 'freshtv398)) : 'freshtv400)) : 'freshtv402)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv403 * _menhir_state * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1326 "src/parsing/dkParser.ml"
            ) * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv404)) : 'freshtv406)
    | MenhirState96 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv413 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1335 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state * 'tv_list_param_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv409 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1347 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_list_param_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv407 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1354 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_list_param_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__6_ : Lexing.position) = _endpos in
            ((let ((((_menhir_stack, _endpos_p_sym_mod_, _menhir_s, (p_sym_mod : 'tv_list_modifier_), _startpos_p_sym_mod_), _endpos_s_, (s : (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1360 "src/parsing/dkParser.ml"
            )), _startpos_s_), _, (p_sym_arg : 'tv_list_param_)), _endpos_a_, _, (a : 'tv_term), _startpos_a_) = _menhir_stack in
            let _v : (
# 237 "src/parsing/dkParser.mly"
      (Syntax.p_command)
# 1365 "src/parsing/dkParser.ml"
            ) = let _endpos = _endpos__6_ in
            let _symbolstartpos = if _startpos_p_sym_mod_ != _endpos_p_sym_mod_ then
              _startpos_p_sym_mod_
            else
              _startpos_s_ in
            let _loc_s_ = (_startpos_s_, _endpos_s_) in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 245 "src/parsing/dkParser.mly"
    (
      let p_sym_mod =
        match List.find_opt is_prop p_sym_mod with
        | Some(_) -> p_sym_mod
        | None -> make_pos _loc_s_ (P_prop Const) :: p_sym_mod
      in
      let p_sym_nam = make_pos _loc_s_ s in
      let p_sym_typ = Some a in
      let p_sym_trm = None in
      let p_sym_prf = None in
      let p_sym_def = false in
      make_pos _sloc
        (P_symbol {p_sym_mod;p_sym_nam;p_sym_arg;p_sym_typ;p_sym_trm;p_sym_prf
                   ;p_sym_def})
    )
# 1390 "src/parsing/dkParser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv408)) : 'freshtv410)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv411 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1400 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_list_param_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv412)) : 'freshtv414)
    | MenhirState101 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv419 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1409 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.DEF ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv415 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1421 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | DkLexer.LEFTPAR ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState103 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.QID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState103 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.TYPE ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState103 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UID _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState103 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UNDERSCORE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState103 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState103) : 'freshtv416)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv417 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1447 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv418)) : 'freshtv420)
    | MenhirState103 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv427 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1456 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv423 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1468 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv421 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1475 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__8_ : Lexing.position) = _endpos in
            ((let ((((((_menhir_stack, _endpos_p_sym_mod_, _menhir_s, (p_sym_mod : 'tv_list_modifier_), _startpos_p_sym_mod_), _startpos__2_), _endpos_s_, (s : (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1481 "src/parsing/dkParser.ml"
            )), _startpos_s_), _), _endpos_a_, _, (a : 'tv_term), _startpos_a_), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
            let _v : (
# 237 "src/parsing/dkParser.mly"
      (Syntax.p_command)
# 1486 "src/parsing/dkParser.ml"
            ) = let _endpos = _endpos__8_ in
            let _symbolstartpos = if _startpos_p_sym_mod_ != _endpos_p_sym_mod_ then
              _startpos_p_sym_mod_
            else
              _startpos__2_ in
            let _loc_s_ = (_startpos_s_, _endpos_s_) in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 320 "src/parsing/dkParser.mly"
    (
      let p_sym_mod = make_pos _loc_s_ P_opaq :: p_sym_mod in
      let p_sym_nam = make_pos _loc_s_ s in
      let p_sym_arg = [] in
      let p_sym_typ = Some a in
      let p_sym_trm = Some t in
      let p_sym_prf = None in
      let p_sym_def = true in
      make_pos _sloc
        (P_symbol {p_sym_mod;p_sym_nam;p_sym_arg;p_sym_typ;p_sym_trm;p_sym_prf
                   ;p_sym_def})
    )
# 1508 "src/parsing/dkParser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv422)) : 'freshtv424)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv425 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1518 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv426)) : 'freshtv428)
    | MenhirState109 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv433 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1527 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.DEF ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((('freshtv429 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1539 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | DkLexer.LEFTPAR ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.QID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState111 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.TYPE ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UID _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState111 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UNDERSCORE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState111) : 'freshtv430)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((('freshtv431 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1565 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv432)) : 'freshtv434)
    | MenhirState111 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((((('freshtv441 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1574 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((((('freshtv437 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1586 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((((('freshtv435 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1593 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__9_ : Lexing.position) = _endpos in
            ((let ((((((_menhir_stack, _endpos_p_sym_mod_, _menhir_s, (p_sym_mod : 'tv_list_modifier_), _startpos_p_sym_mod_), _startpos__2_), _endpos_s_, (s : (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1599 "src/parsing/dkParser.ml"
            )), _startpos_s_), _, (p_sym_arg : 'tv_nonempty_list_param_)), _endpos_a_, _, (a : 'tv_term), _startpos_a_), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
            let _v : (
# 237 "src/parsing/dkParser.mly"
      (Syntax.p_command)
# 1604 "src/parsing/dkParser.ml"
            ) = let _endpos = _endpos__9_ in
            let _symbolstartpos = if _startpos_p_sym_mod_ != _endpos_p_sym_mod_ then
              _startpos_p_sym_mod_
            else
              _startpos__2_ in
            let _loc_s_ = (_startpos_s_, _endpos_s_) in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 334 "src/parsing/dkParser.mly"
    (
      let p_sym_mod = make_pos _loc_s_ P_opaq :: p_sym_mod in
      let p_sym_nam = make_pos _loc_s_ s in
      let p_sym_typ = Some a in
      let p_sym_trm = Some t in
      let p_sym_prf = None in
      let p_sym_def = true in
      make_pos _sloc
        (P_symbol {p_sym_mod;p_sym_nam;p_sym_arg;p_sym_typ;p_sym_trm;p_sym_prf
                   ;p_sym_def})
    )
# 1625 "src/parsing/dkParser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv436)) : 'freshtv438)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((((('freshtv439 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1635 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv440)) : 'freshtv442)
    | MenhirState116 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv449 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1644 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv445 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1656 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv443 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1663 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__6_ : Lexing.position) = _endpos in
            ((let (((((_menhir_stack, _endpos_p_sym_mod_, _menhir_s, (p_sym_mod : 'tv_list_modifier_), _startpos_p_sym_mod_), _startpos__2_), _endpos_s_, (s : (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1669 "src/parsing/dkParser.ml"
            )), _startpos_s_), _), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
            let _v : (
# 237 "src/parsing/dkParser.mly"
      (Syntax.p_command)
# 1674 "src/parsing/dkParser.ml"
            ) = let _endpos = _endpos__6_ in
            let _symbolstartpos = if _startpos_p_sym_mod_ != _endpos_p_sym_mod_ then
              _startpos_p_sym_mod_
            else
              _startpos__2_ in
            let _loc_s_ = (_startpos_s_, _endpos_s_) in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 285 "src/parsing/dkParser.mly"
    (
      let p_sym_nam = make_pos _loc_s_ s in
      let p_sym_arg = [] in
      let p_sym_typ = None in
      let p_sym_trm = Some t in
      let p_sym_prf = None in
      let p_sym_def = true in
      make_pos _sloc
        (P_symbol {p_sym_mod;p_sym_nam;p_sym_arg;p_sym_typ;p_sym_trm;p_sym_prf
                   ;p_sym_def})
    )
# 1695 "src/parsing/dkParser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv444)) : 'freshtv446)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv447 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1705 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv448)) : 'freshtv450)
    | MenhirState119 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv459 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1714 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.DEF ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv451 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1726 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | DkLexer.LEFTPAR ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.QID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState122 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.TYPE ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UID _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState122 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UNDERSCORE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState122) : 'freshtv452)
        | DkLexer.DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv455 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1750 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv453 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1757 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__6_ : Lexing.position) = _endpos in
            ((let (((((_menhir_stack, _endpos_p_sym_mod_, _menhir_s, (p_sym_mod : 'tv_list_modifier_), _startpos_p_sym_mod_), _startpos__2_), _endpos_s_, (s : (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1763 "src/parsing/dkParser.ml"
            )), _startpos_s_), _), _endpos_a_, _, (a : 'tv_term), _startpos_a_) = _menhir_stack in
            let _v : (
# 237 "src/parsing/dkParser.mly"
      (Syntax.p_command)
# 1768 "src/parsing/dkParser.ml"
            ) = let _endpos = _endpos__6_ in
            let _symbolstartpos = if _startpos_p_sym_mod_ != _endpos_p_sym_mod_ then
              _startpos_p_sym_mod_
            else
              _startpos__2_ in
            let _loc_s_ = (_startpos_s_, _endpos_s_) in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 261 "src/parsing/dkParser.mly"
    (
      let p_sym_nam = make_pos _loc_s_ s in
      let p_sym_arg = [] in
      let p_sym_typ = Some a in
      let p_sym_trm = None in
      let p_sym_prf = None in
      let p_sym_def = false in
      make_pos _sloc
        (P_symbol {p_sym_mod;p_sym_nam;p_sym_arg;p_sym_typ;p_sym_trm;p_sym_prf
                   ;p_sym_def})
    )
# 1789 "src/parsing/dkParser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv454)) : 'freshtv456)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv457 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1799 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv458)) : 'freshtv460)
    | MenhirState122 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv467 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1808 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv463 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1820 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv461 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1827 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__8_ : Lexing.position) = _endpos in
            ((let ((((((_menhir_stack, _endpos_p_sym_mod_, _menhir_s, (p_sym_mod : 'tv_list_modifier_), _startpos_p_sym_mod_), _startpos__2_), _endpos_s_, (s : (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1833 "src/parsing/dkParser.ml"
            )), _startpos_s_), _), _endpos_a_, _, (a : 'tv_term), _startpos_a_), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
            let _v : (
# 237 "src/parsing/dkParser.mly"
      (Syntax.p_command)
# 1838 "src/parsing/dkParser.ml"
            ) = let _endpos = _endpos__8_ in
            let _symbolstartpos = if _startpos_p_sym_mod_ != _endpos_p_sym_mod_ then
              _startpos_p_sym_mod_
            else
              _startpos__2_ in
            let _loc_s_ = (_startpos_s_, _endpos_s_) in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 273 "src/parsing/dkParser.mly"
    (
      let p_sym_nam = make_pos _loc_s_ s in
      let p_sym_arg = [] in
      let p_sym_typ = Some a in
      let p_sym_trm = Some t in
      let p_sym_prf = None in
      let p_sym_def = true in
      make_pos _sloc
        (P_symbol {p_sym_mod;p_sym_nam;p_sym_arg;p_sym_typ;p_sym_trm;p_sym_prf
                   ;p_sym_def})
    )
# 1859 "src/parsing/dkParser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv462)) : 'freshtv464)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv465 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1869 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv466)) : 'freshtv468)
    | MenhirState126 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv475 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1878 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((('freshtv471 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1890 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((('freshtv469 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1897 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__7_ : Lexing.position) = _endpos in
            ((let (((((_menhir_stack, _endpos_p_sym_mod_, _menhir_s, (p_sym_mod : 'tv_list_modifier_), _startpos_p_sym_mod_), _startpos__2_), _endpos_s_, (s : (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1903 "src/parsing/dkParser.ml"
            )), _startpos_s_), _, (p_sym_arg : 'tv_nonempty_list_param_)), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
            let _v : (
# 237 "src/parsing/dkParser.mly"
      (Syntax.p_command)
# 1908 "src/parsing/dkParser.ml"
            ) = let _endpos = _endpos__7_ in
            let _symbolstartpos = if _startpos_p_sym_mod_ != _endpos_p_sym_mod_ then
              _startpos_p_sym_mod_
            else
              _startpos__2_ in
            let _loc_s_ = (_startpos_s_, _endpos_s_) in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 309 "src/parsing/dkParser.mly"
    (
      let p_sym_nam = make_pos _loc_s_ s in
      let p_sym_typ = None in
      let p_sym_trm = Some t in
      let p_sym_prf = None in
      let p_sym_def = true in
      make_pos _sloc
        (P_symbol {p_sym_mod;p_sym_nam;p_sym_arg;p_sym_typ;p_sym_trm;p_sym_prf
                   ;p_sym_def})
    )
# 1928 "src/parsing/dkParser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv470)) : 'freshtv472)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((('freshtv473 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1938 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv474)) : 'freshtv476)
    | MenhirState129 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv481 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1947 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.DEF ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((('freshtv477 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1959 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | DkLexer.LEFTPAR ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.QID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState131 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.TYPE ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UID _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState131 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UNDERSCORE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState131) : 'freshtv478)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((('freshtv479 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1985 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv480)) : 'freshtv482)
    | MenhirState131 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((((('freshtv489 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 1994 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((((('freshtv485 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2006 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((((('freshtv483 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2013 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__9_ : Lexing.position) = _endpos in
            ((let ((((((_menhir_stack, _endpos_p_sym_mod_, _menhir_s, (p_sym_mod : 'tv_list_modifier_), _startpos_p_sym_mod_), _startpos__2_), _endpos_s_, (s : (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2019 "src/parsing/dkParser.ml"
            )), _startpos_s_), _, (p_sym_arg : 'tv_nonempty_list_param_)), _endpos_a_, _, (a : 'tv_term), _startpos_a_), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
            let _v : (
# 237 "src/parsing/dkParser.mly"
      (Syntax.p_command)
# 2024 "src/parsing/dkParser.ml"
            ) = let _endpos = _endpos__9_ in
            let _symbolstartpos = if _startpos_p_sym_mod_ != _endpos_p_sym_mod_ then
              _startpos_p_sym_mod_
            else
              _startpos__2_ in
            let _loc_s_ = (_startpos_s_, _endpos_s_) in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 298 "src/parsing/dkParser.mly"
    (
      let p_sym_nam = make_pos _loc_s_ s in
      let p_sym_typ = Some a in
      let p_sym_trm = Some t in
      let p_sym_prf = None in
      let p_sym_def = true in
      make_pos _sloc
        (P_symbol {p_sym_mod;p_sym_nam;p_sym_arg;p_sym_typ;p_sym_trm;p_sym_prf
                   ;p_sym_def})
    )
# 2044 "src/parsing/dkParser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv484)) : 'freshtv486)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((((('freshtv487 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2054 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv488)) : 'freshtv490)
    | _ ->
        _menhir_fail ()

and _menhir_reduce54 : _menhir_env -> ('ttv_tail * _menhir_state) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let ((_menhir_stack, _menhir_s), _endpos_a_, _, (a : 'tv_aterm), _startpos_a_) = _menhir_stack in
    let _v : 'tv_type_annot = 
# 414 "src/parsing/dkParser.mly"
                  ( a )
# 2067 "src/parsing/dkParser.ml"
     in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv279) = _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_type_annot) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv277) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_type_annot) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv275) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((x : 'tv_type_annot) : 'tv_type_annot) = _v in
    ((let _v : 'tv_option_type_annot_ = 
# 116 "<standard.mly>"
    ( Some x )
# 2084 "src/parsing/dkParser.ml"
     in
    _menhir_goto_option_type_annot_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv276)) : 'freshtv278)) : 'freshtv280)

and _menhir_run17 : _menhir_env -> (('ttv_tail * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2091 "src/parsing/dkParser.ml"
) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | DkLexer.LEFTPAR ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DkLexer.QID _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState17 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DkLexer.TYPE ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState17 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DkLexer.UID _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState17 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DkLexer.UNDERSCORE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState17 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState17

and _menhir_reduce25 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_list_param_ = 
# 211 "<standard.mly>"
    ( [] )
# 2118 "src/parsing/dkParser.ml"
     in
    _menhir_goto_list_param_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run88 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | DkLexer.UID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv271 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let (_v : (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2135 "src/parsing/dkParser.ml"
        )) = _v in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv267 * _menhir_state * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2147 "src/parsing/dkParser.ml"
            ) * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | DkLexer.LEFTPAR ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.QID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState90 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.TYPE ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UID _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState90 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UNDERSCORE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState90) : 'freshtv268)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv269 * _menhir_state * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2173 "src/parsing/dkParser.ml"
            ) * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, _), _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv270)) : 'freshtv272)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv273 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv274)

and _menhir_goto_option___anonymous_0_ : _menhir_env -> 'ttv_tail -> 'tv_option___anonymous_0_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv265 * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2191 "src/parsing/dkParser.ml"
    ) * Lexing.position) = Obj.magic _menhir_stack in
    let (_v : 'tv_option___anonymous_0_) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv263 * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2198 "src/parsing/dkParser.ml"
    ) * Lexing.position) = Obj.magic _menhir_stack in
    let ((ao : 'tv_option___anonymous_0_) : 'tv_option___anonymous_0_) = _v in
    ((let (_menhir_stack, _endpos_x_, _menhir_s, (x : (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2204 "src/parsing/dkParser.ml"
    )), _startpos_x_) = _menhir_stack in
    let _v : 'tv_context_item = let _loc_x_ = (_startpos_x_, _endpos_x_) in
    
# 395 "src/parsing/dkParser.mly"
                                        ( (make_pos _loc_x_ x, ao) )
# 2210 "src/parsing/dkParser.ml"
     in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv261) = _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_context_item) = _v in
    ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv259 * _menhir_state * 'tv_context_item) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | DkLexer.COMMA ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv253 * _menhir_state * 'tv_context_item) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.UID _v ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState49 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState49) : 'freshtv254)
    | DkLexer.RIGHTSQU ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv255 * _menhir_state * 'tv_context_item) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (x : 'tv_context_item)) = _menhir_stack in
        let _v : 'tv_separated_nonempty_list_COMMA_context_item_ = 
# 241 "<standard.mly>"
    ( [ x ] )
# 2241 "src/parsing/dkParser.ml"
         in
        _menhir_goto_separated_nonempty_list_COMMA_context_item_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv256)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv257 * _menhir_state * 'tv_context_item) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv258)) : 'freshtv260)) : 'freshtv262)) : 'freshtv264)) : 'freshtv266)

and _menhir_goto_option_type_annot_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_option_type_annot_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState13 | MenhirState19 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv245 * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2261 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state * 'tv_option_type_annot_) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.FATARROW ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv241 * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2271 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_option_type_annot_) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | DkLexer.LEFTPAR ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState31 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.QID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState31 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.TYPE ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState31 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UID _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState31 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UNDERSCORE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState31 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState31) : 'freshtv242)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv243 * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2297 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state * 'tv_option_type_annot_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv244)) : 'freshtv246)
    | MenhirState6 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv251 * Lexing.position * _menhir_state * Lexing.position) * _menhir_state * 'tv_option_type_annot_) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.FATARROW ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv247 * Lexing.position * _menhir_state * Lexing.position) * _menhir_state * 'tv_option_type_annot_) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | DkLexer.LEFTPAR ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.QID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState38 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.TYPE ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UID _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState38 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UNDERSCORE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState38) : 'freshtv248)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv249 * Lexing.position * _menhir_state * Lexing.position) * _menhir_state * 'tv_option_type_annot_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv250)) : 'freshtv252)
    | _ ->
        _menhir_fail ()

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_goto_aterm : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_aterm -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState14 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv219 * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2351 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | DkLexer.LEFTPAR ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.QID _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState16 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.TYPE ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState16 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UID _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState16 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UNDERSCORE ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState16 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.FATARROW ->
            _menhir_reduce54 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState16) : 'freshtv220)
    | MenhirState20 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv227 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2379 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.ARROW ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | DkLexer.LEFTPAR ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState21 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.QID _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState21 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.RIGHTPAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv225 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2395 "src/parsing/dkParser.ml"
            ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let (_menhir_s : _menhir_state) = MenhirState21 in
            ((let _menhir_stack = (_menhir_stack, _endpos, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | DkLexer.ARROW ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (((('freshtv221 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2408 "src/parsing/dkParser.ml"
                ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) * Lexing.position * _menhir_state) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | DkLexer.LEFTPAR ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | DkLexer.QID _v ->
                    _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState23 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | DkLexer.TYPE ->
                    _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState23 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | DkLexer.UID _v ->
                    _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState23 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | DkLexer.UNDERSCORE ->
                    _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState23 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState23) : 'freshtv222)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (((('freshtv223 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2434 "src/parsing/dkParser.ml"
                ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) * Lexing.position * _menhir_state) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _, _menhir_s) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv224)) : 'freshtv226)
        | DkLexer.TYPE ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState21 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UID _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState21 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UNDERSCORE ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState21 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.FATARROW ->
            _menhir_reduce54 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState21) : 'freshtv228)
    | MenhirState129 | MenhirState131 | MenhirState126 | MenhirState119 | MenhirState122 | MenhirState116 | MenhirState109 | MenhirState111 | MenhirState101 | MenhirState103 | MenhirState96 | MenhirState90 | MenhirState77 | MenhirState74 | MenhirState65 | MenhirState68 | MenhirState53 | MenhirState62 | MenhirState44 | MenhirState46 | MenhirState5 | MenhirState38 | MenhirState12 | MenhirState17 | MenhirState18 | MenhirState31 | MenhirState23 | MenhirState25 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv231 * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.LEFTPAR ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.QID _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState27 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.TYPE ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState27 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UID _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState27 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UNDERSCORE ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState27 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.ARROW | DkLexer.COMMA | DkLexer.DEF | DkLexer.DOT | DkLexer.LEFTSQU | DkLexer.LONGARROW | DkLexer.RIGHTPAR | DkLexer.RIGHTSQU ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv229 * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _endpos_t_, _menhir_s, (t : 'tv_aterm), _startpos_t_) = _menhir_stack in
            let _startpos = _startpos_t_ in
            let _endpos = _endpos_t_ in
            let _v : 'tv_term = 
# 417 "src/parsing/dkParser.mly"
            ( t )
# 2475 "src/parsing/dkParser.ml"
             in
            _menhir_goto_term _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv230)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState27) : 'freshtv232)
    | MenhirState7 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv233 * _menhir_state) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.LEFTPAR ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.QID _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState36 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.TYPE ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState36 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UID _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState36 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UNDERSCORE ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState36 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.FATARROW ->
            _menhir_reduce54 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState36) : 'freshtv234)
    | MenhirState72 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv239 * _menhir_state * (
# 203 "src/parsing/dkParser.mly"
       (bool)
# 2509 "src/parsing/dkParser.ml"
        ) * Lexing.position) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv235 * _menhir_state * (
# 203 "src/parsing/dkParser.mly"
       (bool)
# 2519 "src/parsing/dkParser.ml"
            ) * Lexing.position) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState73 in
            ((let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | DkLexer.LEFTPAR ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.QID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState77 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.TYPE ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UID _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState77 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UNDERSCORE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState77) : 'freshtv236)
        | DkLexer.EQUAL ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv237 * _menhir_state * (
# 203 "src/parsing/dkParser.mly"
       (bool)
# 2545 "src/parsing/dkParser.ml"
            ) * Lexing.position) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState73 in
            ((let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | DkLexer.LEFTPAR ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.QID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState74 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.TYPE ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState74 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UID _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState74 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UNDERSCORE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState74 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState74) : 'freshtv238)
        | DkLexer.LEFTPAR ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState73 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.QID _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState73 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.TYPE ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState73 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UID _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState73 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UNDERSCORE ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState73 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState73) : 'freshtv240)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_modifier_ : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_list_modifier_ -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState84 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv193 * Lexing.position * _menhir_state * 'tv_modifier * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv191 * Lexing.position * _menhir_state * 'tv_modifier * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _endpos_x_, _menhir_s, (x : 'tv_modifier), _startpos_x_), _endpos_xs_, _, (xs : 'tv_list_modifier_), _startpos_xs_) = _menhir_stack in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_xs_ in
        let _v : 'tv_list_modifier_ = 
# 213 "<standard.mly>"
    ( x :: xs )
# 2598 "src/parsing/dkParser.ml"
         in
        _menhir_goto_list_modifier_ _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv192)) : 'freshtv194)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv217 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.KW_DEF ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv203 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) = Obj.magic _menhir_stack in
            let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            ((let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | DkLexer.UID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv199 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
                let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let (_v : (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2622 "src/parsing/dkParser.ml"
                )) = _v in
                let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                ((let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | DkLexer.COLON ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv195 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2634 "src/parsing/dkParser.ml"
                    ) * Lexing.position) = Obj.magic _menhir_stack in
                    let (_menhir_s : _menhir_state) = MenhirState115 in
                    ((let _menhir_stack = (_menhir_stack, _menhir_s) in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    match _tok with
                    | DkLexer.LEFTPAR ->
                        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState119 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | DkLexer.QID _v ->
                        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState119 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | DkLexer.TYPE ->
                        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState119 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | DkLexer.UID _v ->
                        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState119 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | DkLexer.UNDERSCORE ->
                        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState119 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState119) : 'freshtv196)
                | DkLexer.DEF ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv197 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2660 "src/parsing/dkParser.ml"
                    ) * Lexing.position) = Obj.magic _menhir_stack in
                    let (_menhir_s : _menhir_state) = MenhirState115 in
                    ((let _menhir_stack = (_menhir_stack, _menhir_s) in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    match _tok with
                    | DkLexer.LEFTPAR ->
                        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | DkLexer.QID _v ->
                        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState116 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | DkLexer.TYPE ->
                        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState116 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | DkLexer.UID _v ->
                        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState116 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | DkLexer.UNDERSCORE ->
                        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState116 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState116) : 'freshtv198)
                | DkLexer.LEFTPAR ->
                    _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState115 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState115) : 'freshtv200)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv201 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv202)) : 'freshtv204)
        | DkLexer.KW_THM ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv211 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) = Obj.magic _menhir_stack in
            let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            ((let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | DkLexer.UID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv207 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
                let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let (_v : (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2709 "src/parsing/dkParser.ml"
                )) = _v in
                let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                ((let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | DkLexer.COLON ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv205 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2721 "src/parsing/dkParser.ml"
                    ) * Lexing.position) = Obj.magic _menhir_stack in
                    let (_menhir_s : _menhir_state) = MenhirState100 in
                    ((let _menhir_stack = (_menhir_stack, _menhir_s) in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    match _tok with
                    | DkLexer.LEFTPAR ->
                        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState101 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | DkLexer.QID _v ->
                        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | DkLexer.TYPE ->
                        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | DkLexer.UID _v ->
                        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | DkLexer.UNDERSCORE ->
                        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState101) : 'freshtv206)
                | DkLexer.LEFTPAR ->
                    _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState100) : 'freshtv208)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv209 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv210)) : 'freshtv212)
        | DkLexer.UID _v ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv213 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let (_v : (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2762 "src/parsing/dkParser.ml"
            )) = _v in
            let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            ((let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | DkLexer.LEFTPAR ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.COLON ->
                _menhir_reduce25 _menhir_env (Obj.magic _menhir_stack) MenhirState87
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState87) : 'freshtv214)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv215 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv216)) : 'freshtv218)
    | _ ->
        _menhir_fail ()

and _menhir_goto_loption_separated_nonempty_list_COMMA_context_item__ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_loption_separated_nonempty_list_COMMA_context_item__ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv189 * _menhir_state * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_COMMA_context_item__) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | DkLexer.RIGHTSQU ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv185 * _menhir_state * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_COMMA_context_item__) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        ((let _menhir_stack = (_menhir_stack, _endpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.LEFTPAR ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.QID _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState44 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.TYPE ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UID _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState44 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UNDERSCORE ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState44) : 'freshtv186)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv187 * _menhir_state * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_COMMA_context_item__) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv188)) : 'freshtv190)

and _menhir_run4 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2828 "src/parsing/dkParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | DkLexer.COLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv179) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.LEFTPAR ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState5 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.QID _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState5 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.TYPE ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState5 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UID _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState5 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UNDERSCORE ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState5 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState5) : 'freshtv180)
    | DkLexer.COMMA | DkLexer.RIGHTSQU ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv181) = Obj.magic _menhir_stack in
        ((let _v : 'tv_option___anonymous_0_ = 
# 114 "<standard.mly>"
    ( None )
# 2861 "src/parsing/dkParser.ml"
         in
        _menhir_goto_option___anonymous_0_ _menhir_env _menhir_stack _v) : 'freshtv182)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv183 * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2871 "src/parsing/dkParser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv184)

and _menhir_goto_modifier : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_modifier -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv177 * Lexing.position * _menhir_state * 'tv_modifier * Lexing.position) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | DkLexer.KW_INJ ->
        _menhir_run52 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState84 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DkLexer.KW_PRV ->
        _menhir_run51 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState84 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DkLexer.KW_DEF | DkLexer.KW_THM | DkLexer.UID _ ->
        _menhir_reduce23 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState84) : 'freshtv178)

and _menhir_goto_eval_config : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_eval_config -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState53 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv173 * _menhir_state * Lexing.position) * _menhir_state * 'tv_eval_config) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.LEFTPAR ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState62 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.QID _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState62 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.TYPE ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState62 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UID _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState62 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UNDERSCORE ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState62 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState62) : 'freshtv174)
    | MenhirState65 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv175 * _menhir_state * Lexing.position) * _menhir_state * 'tv_eval_config) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.LEFTPAR ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.QID _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState68 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.TYPE ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState68 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UID _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState68 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UNDERSCORE ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState68 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState68) : 'freshtv176)
    | _ ->
        _menhir_fail ()

and _menhir_reduce37 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_option_type_annot_ = 
# 114 "<standard.mly>"
    ( None )
# 2947 "src/parsing/dkParser.ml"
     in
    _menhir_goto_option_type_annot_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce45 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _endpos__1_, _menhir_s, _startpos__1_) = _menhir_stack in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_sterm = let _endpos = _endpos__1_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 405 "src/parsing/dkParser.mly"
               ( make_pos _sloc P_Wild )
# 2962 "src/parsing/dkParser.ml"
     in
    _menhir_goto_sterm _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_reduce44 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2969 "src/parsing/dkParser.ml"
) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _endpos_id_, _menhir_s, (id : (
# 231 "src/parsing/dkParser.mly"
       (string)
# 2975 "src/parsing/dkParser.ml"
    )), _startpos_id_) = _menhir_stack in
    let _startpos = _startpos_id_ in
    let _endpos = _endpos_id_ in
    let _v : 'tv_sterm = let _endpos = _endpos_id_ in
    let _symbolstartpos = _startpos_id_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 404 "src/parsing/dkParser.mly"
             ( make_pos _sloc (P_Iden(make_pos _sloc ([], id), false)) )
# 2985 "src/parsing/dkParser.ml"
     in
    _menhir_goto_sterm _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_goto_sterm : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_sterm -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    match _menhir_s with
    | MenhirState129 | MenhirState131 | MenhirState126 | MenhirState119 | MenhirState122 | MenhirState116 | MenhirState109 | MenhirState111 | MenhirState101 | MenhirState103 | MenhirState96 | MenhirState90 | MenhirState77 | MenhirState74 | MenhirState72 | MenhirState68 | MenhirState65 | MenhirState62 | MenhirState53 | MenhirState44 | MenhirState46 | MenhirState5 | MenhirState38 | MenhirState7 | MenhirState12 | MenhirState17 | MenhirState18 | MenhirState31 | MenhirState23 | MenhirState25 | MenhirState20 | MenhirState14 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv167) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _endpos in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_sterm) = _v in
        let (_startpos : Lexing.position) = _startpos in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv165) = Obj.magic _menhir_stack in
        let (_endpos_t_ : Lexing.position) = _endpos in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let ((t : 'tv_sterm) : 'tv_sterm) = _v in
        let (_startpos_t_ : Lexing.position) = _startpos in
        ((let _startpos = _startpos_t_ in
        let _endpos = _endpos_t_ in
        let _v : 'tv_aterm = 
# 411 "src/parsing/dkParser.mly"
                    ( t )
# 3010 "src/parsing/dkParser.ml"
         in
        _menhir_goto_aterm _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv166)) : 'freshtv168)
    | MenhirState73 | MenhirState36 | MenhirState16 | MenhirState21 | MenhirState27 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv171 * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _endpos in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_sterm) = _v in
        let (_startpos : Lexing.position) = _startpos in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv169 * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos_u_ : Lexing.position) = _endpos in
        let (_ : _menhir_state) = _menhir_s in
        let ((u : 'tv_sterm) : 'tv_sterm) = _v in
        let (_startpos_u_ : Lexing.position) = _startpos in
        ((let (_menhir_stack, _endpos_t_, _menhir_s, (t : 'tv_aterm), _startpos_t_) = _menhir_stack in
        let _startpos = _startpos_t_ in
        let _endpos = _endpos_u_ in
        let _v : 'tv_aterm = let _endpos = _endpos_u_ in
        let _symbolstartpos = _startpos_t_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 410 "src/parsing/dkParser.mly"
                    ( make_pos _sloc (P_Appl(t,u)) )
# 3035 "src/parsing/dkParser.ml"
         in
        _menhir_goto_aterm _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv170)) : 'freshtv172)
    | _ ->
        _menhir_fail ()

and _menhir_reduce23 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let (_, _startpos) = Obj.magic _menhir_stack in
    let _endpos = _startpos in
    let _v : 'tv_list_modifier_ = 
# 211 "<standard.mly>"
    ( [] )
# 3048 "src/parsing/dkParser.ml"
     in
    _menhir_goto_list_modifier_ _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run3 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | DkLexer.UID _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DkLexer.RIGHTSQU ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv163) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState3 in
        ((let _v : 'tv_loption_separated_nonempty_list_COMMA_context_item__ = 
# 142 "<standard.mly>"
    ( [] )
# 3067 "src/parsing/dkParser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_COMMA_context_item__ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv164)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState3

and _menhir_run51 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv161) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_modifier = let _endpos = _endpos__1_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 391 "src/parsing/dkParser.mly"
           ( make_pos _sloc (P_expo(Term.Protec)) )
# 3091 "src/parsing/dkParser.ml"
     in
    _menhir_goto_modifier _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv162)

and _menhir_run52 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv159) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_modifier = let _endpos = _endpos__1_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 392 "src/parsing/dkParser.mly"
           ( make_pos _sloc (P_prop(Term.Injec)) )
# 3111 "src/parsing/dkParser.ml"
     in
    _menhir_goto_modifier _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv160)

and _menhir_run6 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | DkLexer.COLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv157) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState6 in
        ((let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.LEFTPAR ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState7 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.QID _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState7 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.TYPE ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState7 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UID _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState7 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UNDERSCORE ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState7 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState7) : 'freshtv158)
    | DkLexer.ARROW | DkLexer.COMMA | DkLexer.DEF | DkLexer.DOT | DkLexer.LEFTPAR | DkLexer.LEFTSQU | DkLexer.LONGARROW | DkLexer.QID _ | DkLexer.RIGHTPAR | DkLexer.RIGHTSQU | DkLexer.TYPE | DkLexer.UID _ | DkLexer.UNDERSCORE ->
        _menhir_reduce45 _menhir_env (Obj.magic _menhir_stack)
    | DkLexer.FATARROW ->
        _menhir_reduce37 _menhir_env (Obj.magic _menhir_stack) MenhirState6
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState6

and _menhir_run13 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3155 "src/parsing/dkParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | DkLexer.COLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv155 * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3167 "src/parsing/dkParser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState13 in
        ((let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.LEFTPAR ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState14 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.QID _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState14 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.TYPE ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState14 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UID _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState14 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UNDERSCORE ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState14 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState14) : 'freshtv156)
    | DkLexer.ARROW | DkLexer.COMMA | DkLexer.DEF | DkLexer.DOT | DkLexer.LEFTPAR | DkLexer.LEFTSQU | DkLexer.LONGARROW | DkLexer.QID _ | DkLexer.RIGHTPAR | DkLexer.RIGHTSQU | DkLexer.TYPE | DkLexer.UID _ | DkLexer.UNDERSCORE ->
        _menhir_reduce44 _menhir_env (Obj.magic _menhir_stack)
    | DkLexer.FATARROW ->
        _menhir_reduce37 _menhir_env (Obj.magic _menhir_stack) MenhirState13
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState13

and _menhir_run54 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | DkLexer.UID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv151 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let (_v : (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3210 "src/parsing/dkParser.ml"
        )) = _v in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.COMMA ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv143 * _menhir_state * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3222 "src/parsing/dkParser.ml"
            ) * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | DkLexer.UID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv139 * _menhir_state * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3232 "src/parsing/dkParser.ml"
                ) * Lexing.position)) = Obj.magic _menhir_stack in
                let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let (_v : (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3238 "src/parsing/dkParser.ml"
                )) = _v in
                let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                ((let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | DkLexer.RIGHTSQU ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv135 * _menhir_state * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3250 "src/parsing/dkParser.ml"
                    ) * Lexing.position)) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3254 "src/parsing/dkParser.ml"
                    ) * Lexing.position) = Obj.magic _menhir_stack in
                    let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv133 * _menhir_state * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3262 "src/parsing/dkParser.ml"
                    ) * Lexing.position)) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3266 "src/parsing/dkParser.ml"
                    ) * Lexing.position) = Obj.magic _menhir_stack in
                    let (_endpos__5_ : Lexing.position) = _endpos in
                    ((let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos_s1_, (s1 : (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3272 "src/parsing/dkParser.ml"
                    )), _startpos_s1_), _endpos_s2_, (s2 : (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3276 "src/parsing/dkParser.ml"
                    )), _startpos_s2_) = _menhir_stack in
                    let _v : 'tv_eval_config = let _endpos = _endpos__5_ in
                    let _symbolstartpos = _startpos__1_ in
                    let _sloc = (_symbolstartpos, _endpos) in
                    
# 384 "src/parsing/dkParser.mly"
    ( build_strat (locate _sloc) s1 (Some s2) )
# 3284 "src/parsing/dkParser.ml"
                     in
                    _menhir_goto_eval_config _menhir_env _menhir_stack _menhir_s _v) : 'freshtv134)) : 'freshtv136)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv137 * _menhir_state * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3294 "src/parsing/dkParser.ml"
                    ) * Lexing.position)) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3298 "src/parsing/dkParser.ml"
                    ) * Lexing.position) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s, _), _, _, _), _, _, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv138)) : 'freshtv140)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv141 * _menhir_state * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3309 "src/parsing/dkParser.ml"
                ) * Lexing.position)) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s, _), _, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv142)) : 'freshtv144)
        | DkLexer.RIGHTSQU ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv147 * _menhir_state * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3318 "src/parsing/dkParser.ml"
            ) * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv145 * _menhir_state * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3326 "src/parsing/dkParser.ml"
            ) * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__3_ : Lexing.position) = _endpos in
            ((let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_s_, (s : (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3332 "src/parsing/dkParser.ml"
            )), _startpos_s_) = _menhir_stack in
            let _v : 'tv_eval_config = let _endpos = _endpos__3_ in
            let _symbolstartpos = _startpos__1_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 382 "src/parsing/dkParser.mly"
    ( build_strat (locate _sloc) s None )
# 3340 "src/parsing/dkParser.ml"
             in
            _menhir_goto_eval_config _menhir_env _menhir_stack _menhir_s _v) : 'freshtv146)) : 'freshtv148)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv149 * _menhir_state * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3350 "src/parsing/dkParser.ml"
            ) * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, _), _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv150)) : 'freshtv152)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv153 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv154)

and _menhir_run18 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | DkLexer.LEFTPAR ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DkLexer.QID _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState18 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DkLexer.TYPE ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DkLexer.UID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv131 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let (_menhir_s : _menhir_state) = MenhirState18 in
        let (_v : (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3382 "src/parsing/dkParser.ml"
        )) = _v in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv129 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3394 "src/parsing/dkParser.ml"
            ) * Lexing.position) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState19 in
            ((let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | DkLexer.LEFTPAR ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.QID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState20 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.TYPE ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState20 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UID _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState20 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DkLexer.UNDERSCORE ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState20 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState20) : 'freshtv130)
        | DkLexer.ARROW | DkLexer.LEFTPAR | DkLexer.QID _ | DkLexer.RIGHTPAR | DkLexer.TYPE | DkLexer.UID _ | DkLexer.UNDERSCORE ->
            _menhir_reduce44 _menhir_env (Obj.magic _menhir_stack)
        | DkLexer.FATARROW ->
            _menhir_reduce37 _menhir_env (Obj.magic _menhir_stack) MenhirState19
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState19) : 'freshtv132)
    | DkLexer.UNDERSCORE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState18

and _menhir_goto_command : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 237 "src/parsing/dkParser.mly"
      (Syntax.p_command)
# 3433 "src/parsing/dkParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv127) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : (
# 237 "src/parsing/dkParser.mly"
      (Syntax.p_command)
# 3442 "src/parsing/dkParser.ml"
    )) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv125) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((_1 : (
# 237 "src/parsing/dkParser.mly"
      (Syntax.p_command)
# 3450 "src/parsing/dkParser.ml"
    )) : (
# 237 "src/parsing/dkParser.mly"
      (Syntax.p_command)
# 3454 "src/parsing/dkParser.ml"
    )) = _v in
    (Obj.magic _1 : 'freshtv126)) : 'freshtv128)

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState131 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv25 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3466 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv26)
    | MenhirState129 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv27 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3475 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv28)
    | MenhirState126 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv29 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3484 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv30)
    | MenhirState122 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv31 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3493 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv32)
    | MenhirState119 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv33 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3502 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv34)
    | MenhirState116 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv35 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3511 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv36)
    | MenhirState115 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv37 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3520 "src/parsing/dkParser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _, _menhir_s, _, _), _), _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv38)
    | MenhirState111 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv39 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3529 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv40)
    | MenhirState109 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv41 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3538 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state * 'tv_nonempty_list_param_)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv42)
    | MenhirState106 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv43 * _menhir_state * 'tv_param) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv44)
    | MenhirState103 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv45 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3552 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv46)
    | MenhirState101 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv47 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3561 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv48)
    | MenhirState100 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv49 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3570 "src/parsing/dkParser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _, _menhir_s, _, _), _), _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv50)
    | MenhirState96 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv51 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3579 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state * 'tv_list_param_)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv52)
    | MenhirState93 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv53 * _menhir_state * 'tv_param) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv54)
    | MenhirState90 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv55 * _menhir_state * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3593 "src/parsing/dkParser.ml"
        ) * Lexing.position)) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv56)
    | MenhirState87 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv57 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3602 "src/parsing/dkParser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _, _), _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv58)
    | MenhirState84 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv59 * Lexing.position * _menhir_state * 'tv_modifier * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv60)
    | MenhirState80 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv61 * _menhir_state * 'tv_rule * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv62)
    | MenhirState77 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv63 * _menhir_state * (
# 203 "src/parsing/dkParser.mly"
       (bool)
# 3621 "src/parsing/dkParser.ml"
        ) * Lexing.position) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv64)
    | MenhirState74 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv65 * _menhir_state * (
# 203 "src/parsing/dkParser.mly"
       (bool)
# 3630 "src/parsing/dkParser.ml"
        ) * Lexing.position) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv66)
    | MenhirState73 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv67 * _menhir_state * (
# 203 "src/parsing/dkParser.mly"
       (bool)
# 3639 "src/parsing/dkParser.ml"
        ) * Lexing.position) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv68)
    | MenhirState72 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv69 * _menhir_state * (
# 203 "src/parsing/dkParser.mly"
       (bool)
# 3648 "src/parsing/dkParser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv70)
    | MenhirState68 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv71 * _menhir_state * Lexing.position) * _menhir_state * 'tv_eval_config) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv72)
    | MenhirState65 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv73 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv74)
    | MenhirState62 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv75 * _menhir_state * Lexing.position) * _menhir_state * 'tv_eval_config) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv76)
    | MenhirState53 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv77 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv78)
    | MenhirState49 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv79 * _menhir_state * 'tv_context_item)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv80)
    | MenhirState46 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv81 * _menhir_state * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_COMMA_context_item__) * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv82)
    | MenhirState44 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv83 * _menhir_state * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_COMMA_context_item__) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv84)
    | MenhirState38 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv85 * Lexing.position * _menhir_state * Lexing.position) * _menhir_state * 'tv_option_type_annot_)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv86)
    | MenhirState36 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv87 * _menhir_state) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv88)
    | MenhirState31 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv89 * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3702 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state * 'tv_option_type_annot_)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv90)
    | MenhirState27 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv91 * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv92)
    | MenhirState25 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv93 * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv94)
    | MenhirState23 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv95 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3721 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) * Lexing.position * _menhir_state)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv96)
    | MenhirState21 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv97 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3730 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv98)
    | MenhirState20 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv99 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3739 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv100)
    | MenhirState19 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv101 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3748 "src/parsing/dkParser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv102)
    | MenhirState18 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv103 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv104)
    | MenhirState17 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv105 * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3762 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv106)
    | MenhirState16 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv107 * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3771 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_aterm * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv108)
    | MenhirState14 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv109 * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3780 "src/parsing/dkParser.ml"
        ) * Lexing.position) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv110)
    | MenhirState13 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv111 * Lexing.position * _menhir_state * (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3789 "src/parsing/dkParser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv112)
    | MenhirState12 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv113 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv114)
    | MenhirState7 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv115 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv116)
    | MenhirState6 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv117 * Lexing.position * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv118)
    | MenhirState5 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv119) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv120)
    | MenhirState3 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv121 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv122)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv123) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv124)

and _menhir_run8 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce45 _menhir_env (Obj.magic _menhir_stack)

and _menhir_run9 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 231 "src/parsing/dkParser.mly"
       (string)
# 3831 "src/parsing/dkParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce44 _menhir_env (Obj.magic _menhir_stack)

and _menhir_run10 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv23) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_sterm = let _endpos = _endpos__1_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 406 "src/parsing/dkParser.mly"
            ( make_pos _sloc P_Type )
# 3854 "src/parsing/dkParser.ml"
     in
    _menhir_goto_sterm _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv24)

and _menhir_run11 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 232 "src/parsing/dkParser.mly"
       (Syntax.qident)
# 3861 "src/parsing/dkParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv21) = Obj.magic _menhir_stack in
    let (_endpos_qid_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((qid : (
# 232 "src/parsing/dkParser.mly"
       (Syntax.qident)
# 3872 "src/parsing/dkParser.ml"
    )) : (
# 232 "src/parsing/dkParser.mly"
       (Syntax.qident)
# 3876 "src/parsing/dkParser.ml"
    )) = _v in
    let (_startpos_qid_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos_qid_ in
    let _endpos = _endpos_qid_ in
    let _v : 'tv_sterm = let _endpos = _endpos_qid_ in
    let _symbolstartpos = _startpos_qid_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 403 "src/parsing/dkParser.mly"
            ( make_pos _sloc (P_Iden(make_pos _sloc qid, false)) )
# 3887 "src/parsing/dkParser.ml"
     in
    _menhir_goto_sterm _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv22)

and _menhir_run12 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | DkLexer.LEFTPAR ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState12 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DkLexer.QID _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState12 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DkLexer.TYPE ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState12 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DkLexer.UID _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState12 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DkLexer.UNDERSCORE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState12 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState12

and _menhir_discard : _menhir_env -> _menhir_env =
  fun _menhir_env ->
    let lexer = _menhir_env._menhir_lexer in
    let lexbuf = _menhir_env._menhir_lexbuf in
    let _tok = lexer lexbuf in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    }

and command : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (
# 237 "src/parsing/dkParser.mly"
      (Syntax.p_command)
# 3927 "src/parsing/dkParser.ml"
) =
  fun lexer lexbuf ->
    let _menhir_env = {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = Obj.magic ();
      _menhir_error = false;
    } in
    Obj.magic (let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv19) = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    ((let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | DkLexer.ASSERT _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState0 in
        let (_v : (
# 203 "src/parsing/dkParser.mly"
       (bool)
# 3948 "src/parsing/dkParser.ml"
        )) = _v in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.LEFTPAR ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.QID _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState72 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.TYPE ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UID _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState72 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UNDERSCORE ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState72) : 'freshtv2)
    | DkLexer.EOF ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv5) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState0 in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv3) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        ((let _v : (
# 237 "src/parsing/dkParser.mly"
      (Syntax.p_command)
# 3979 "src/parsing/dkParser.ml"
        ) = 
# 376 "src/parsing/dkParser.mly"
        (
      raise End_of_file
    )
# 3985 "src/parsing/dkParser.ml"
         in
        _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv4)) : 'freshtv6)
    | DkLexer.EVAL ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv7) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState0 in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.LEFTPAR ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.LEFTSQU ->
            _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.QID _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState65 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.TYPE ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState65 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UID _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState65 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UNDERSCORE ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState65 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState65) : 'freshtv8)
    | DkLexer.INFER ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv9) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState0 in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.LEFTPAR ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState53 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.LEFTSQU ->
            _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState53 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.QID _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState53 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.TYPE ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState53 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UID _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState53 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DkLexer.UNDERSCORE ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState53 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState53) : 'freshtv10)
    | DkLexer.KW_INJ ->
        _menhir_run52 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DkLexer.KW_PRV ->
        _menhir_run51 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DkLexer.LEFTSQU ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DkLexer.REQUIRE _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv17) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let (_menhir_s : _menhir_state) = MenhirState0 in
        let (_v : (
# 210 "src/parsing/dkParser.mly"
       (Path.t)
# 4052 "src/parsing/dkParser.ml"
        )) = _v in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DkLexer.DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv13 * Lexing.position * _menhir_state * (
# 210 "src/parsing/dkParser.mly"
       (Path.t)
# 4064 "src/parsing/dkParser.ml"
            ) * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv11 * Lexing.position * _menhir_state * (
# 210 "src/parsing/dkParser.mly"
       (Path.t)
# 4071 "src/parsing/dkParser.ml"
            ) * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__2_ : Lexing.position) = _endpos in
            ((let (_menhir_stack, _endpos_r_, _menhir_s, (r : (
# 210 "src/parsing/dkParser.mly"
       (Path.t)
# 4077 "src/parsing/dkParser.ml"
            )), _startpos_r_) = _menhir_stack in
            let _v : (
# 237 "src/parsing/dkParser.mly"
      (Syntax.p_command)
# 4082 "src/parsing/dkParser.ml"
            ) = let _endpos = _endpos__2_ in
            let _symbolstartpos = _startpos_r_ in
            let _loc_r_ = (_startpos_r_, _endpos_r_) in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 375 "src/parsing/dkParser.mly"
                  ( make_pos _sloc (P_require(false, [make_pos _loc_r_ r])) )
# 4090 "src/parsing/dkParser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv12)) : 'freshtv14)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv15 * Lexing.position * _menhir_state * (
# 210 "src/parsing/dkParser.mly"
       (Path.t)
# 4100 "src/parsing/dkParser.ml"
            ) * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv16)) : 'freshtv18)
    | DkLexer.KW_DEF | DkLexer.KW_THM | DkLexer.UID _ ->
        _menhir_reduce23 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0) : 'freshtv20))

# 436 "src/parsing/dkParser.mly"
  

# 4114 "src/parsing/dkParser.ml"

# 269 "<standard.mly>"
  

# 4119 "src/parsing/dkParser.ml"
