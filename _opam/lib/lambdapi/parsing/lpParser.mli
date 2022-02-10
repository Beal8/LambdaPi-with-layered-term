
(* The type of tokens. *)

type token = LpLexer.token

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val id: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.p_qident)

val command: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.p_command)
