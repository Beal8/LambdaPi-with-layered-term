
(* The type of tokens. *)

type token = DkLexer.token

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val command: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.p_command)
