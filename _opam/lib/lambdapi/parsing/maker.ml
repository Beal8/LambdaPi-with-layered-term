open Common
open Core
open Syntax
module T = Term

(* TODO: factorise modules *)

module type BUILDER = sig
  val term: ?sig_st:Sig_state.t -> ?pb:T.problem -> string -> T.term
end

module Lp : BUILDER = struct
let term: ?sig_st:Sig_state.t -> ?pb:T.problem -> string -> Term.term = fun ?sig_st ?pb s ->
  let wrapped = Format.sprintf "compute %s;" s in
  let Pos.{elt=cmd;_} = Stream.next (Parser.parse_string "" wrapped) in
  let pt =
    match cmd with
    | P_query {elt=(P_query_normalize (te,_)); _} -> te
    (**| P_symbol {p_sym_nam = {elt = n;_}; p_sym_typ = Some t} -> *)
    | _ -> assert false
  in
  let sig_st = match sig_st with
  | Some ss -> ss
  | None ->
      let sign = Sig_state.create_sign ["unparse"] in
      Sig_state.of_sign sign
  in
  let pb = match pb with Some pb -> pb | None -> Term.new_problem () in
  let m _ = None in
  Scope.scope_term false sig_st [] pb m m pt
end

module Dk : BUILDER = struct
let term: ?sig_st:Sig_state.t -> ?pb:T.problem -> string -> Term.term = fun ?sig_st ?pb s ->
  let wrapped = Format.sprintf "#EVAL %s." s in
  let Pos.{elt=cmd;_} = Stream.next (Parser.Dk.parse_string "" wrapped) in
  let pt =
    match cmd with
    | P_query {elt=(P_query_normalize (te,_)); _} -> te
    | _ -> assert false
  in
  let sig_st = match sig_st with
  | Some ss -> ss
  | None ->
      let sign = Sig_state.create_sign ["unparse"] in
      Sig_state.of_sign sign
  in
  let pb = match pb with Some pb -> pb | None -> Term.new_problem () in
  let m _ = None in
  Scope.scope_term false sig_st [] pb m m pt
end
