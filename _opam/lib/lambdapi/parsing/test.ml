open Core
open Term
open Bindlib
open Printf
open Timed

let mname m = match m.meta_name with None -> "?" | Some s -> s
let ioption i = match i with None -> "?" | Some i -> string_of_int i

let rec pprint = function
    | Vari t -> sprintf "%s" (name_of t)
    | Type -> sprintf "TYPE"
    | Kind -> sprintf "KIND"
    | Symb s -> sprintf "%s" (s.sym_name)
    | Prod (t, tb) -> sprintf "(Π %s : %s . %s)" (name_of (fst (unbind tb))) (pprint t) (pprint (snd (unbind tb)))
    | Abst (t,tb) -> sprintf "(λ %s : %s.%s)" (name_of (fst (unbind tb))) (pprint t) (pprint (snd (unbind tb)))
    | Appl (t1,t2) -> sprintf "(%s %s)" (pprint t1) (pprint t2)
    | Meta (m,ta) -> sprintf "(%s %s)" (let mname = function
                                                    None -> "?"
                                                  | Some s -> s
                                        in mname m.meta_name)
                                       (pprint_list (Array.to_list ta))
    | Patt (io, s, ta) -> sprintf "(%s %s %s)" (let iname = function
                                                            None -> "?"
                                                          | Some i -> string_of_int i
                                                in iname io)
                                                s
                                                (pprint_list (Array.to_list ta))
    | TEnv (_,ta) -> sprintf "(env = %s %s)" ("term_env") (pprint_list (Array.to_list(ta)))
    | Wild -> sprintf "WILD"
    | TRef tr -> sprintf "%s" (let termoption = function
                                            | None -> "?"
                                            | Some t -> pprint t
                                in termoption ((!) tr))
    | LLet (t1,t2,b) -> sprintf "let %s : %s := %s in %s" (name_of(fst(unbind b))) (pprint t1) (pprint t2) (pprint(snd(unbind b)))

and pprint_list = function
    |[] -> ""
    |t::q -> (pprint t) ^ (pprint_list q)

let rec dprint = function
    |Vari v -> sprintf "(Vari %s)" (name_of v)
    |Type -> sprintf "(Type)"
    |Kind -> sprintf "(Kind)"
    |Symb s -> sprintf "%s" s.sym_name
    |Prod (t,tb) -> sprintf "(Prod (%s,(%s,%s)))" (dprint t) (name_of(fst(unbind tb))) (dprint (snd (unbind tb)))
    |Abst (t,tb) ->  sprintf "(Abst (%s,(%s,%s)))" (dprint t) (name_of(fst(unbind tb))) (dprint (snd (unbind tb)))
    |Appl (t1,t2) -> sprintf "(Appl (%s,%s))" (dprint t1) (dprint t2)
    |Meta (m,ta) -> sprintf "(Meta (%s, (%s)))" (mname m) (Array.fold_left (fun acc t -> if acc = "" then dprint t else acc ^ "," ^ dprint (t)) "" ta)
    |Patt (io,s,ta) -> sprintf "(Patt (%s,%s,%s))" (ioption io) (s) (Array.fold_left (fun acc t -> if acc = "" then dprint t else acc ^ "," ^ dprint(t)) "" ta)
    |Wild -> "Wild"
    |TRef t -> let t = (!)t in begin match t with None -> "(TRef ?)" | Some t -> sprintf "(TRef %s)" (dprint t) end
    |LLet (t1,t2,tb) -> sprintf "(LLet (%s,%S,(%s,%s)))" (dprint t1) (dprint t2) (name_of(fst(unbind tb))) (dprint(snd(unbind tb)))
    |_ -> failwith "pas possible"
