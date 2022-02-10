open Term
open Printf
open Bindlib
open Timed

let i = ref 0

let dcr i =
  i := !i - 1;
  !i

type ltvar = layered_term var

and ltbinder = (layered_term, layered_term) binder

and layered_term =
  | LVari of ltvar * int (** Free variable. *)
  | LType of int (** "TYPE" constant. *)
  | LKind of int (** "KIND" constant. *)
  | LProd of layered_term * ltbinder * int (** Dependent product. *)
  | LAbst of layered_term * ltbinder * int (** Abstraction. *)
  | LAppl of layered_term * layered_term * int (** Term application. *)

let rec find_at i = function
    |t::_ when i = 0 -> t
    |_::q -> find_at (i-1) q
    |[] -> failwith "index out of bounds"

let pprint_index i = if i < 0 then sprintf "?%i" (abs i) else sprintf "%i" i

let var_layer = function
  |LVari (_,i) -> i
  |_ -> failwith "not a var"

let rec dlprint = function
    |LVari (v,i) -> sprintf "(Vari %s,%s)" (name_of v) (pprint_index i)
    |LType i -> sprintf "(Type %s)" (pprint_index i)
    |LKind i -> sprintf "(Kind %s)" (pprint_index i)
    |LProd (t,tb,i) -> let v,tt = unbind tb in sprintf "(Prod (%s,(%s %s,%s)), %s)" (dlprint t) (name_of(v)) (pprint_index (var_layer (unbox (box_var v)))) (dlprint tt) (pprint_index i)
    |LAbst (t,tb,i) ->  let v,tt = unbind tb in sprintf "(Abst (%s,(%s %s,%s)), %s)" (dlprint t) (name_of(v)) (pprint_index (var_layer (unbox (box_var v)))) (dlprint (tt)) (pprint_index i)
    |LAppl (t1,t2, i) -> sprintf "(Appl (%s,%s), %s)" (dlprint t1) (dlprint t2) (pprint_index i)

let rec pprint = function
  |LVari  (v,i) -> sprintf "(%s,%s)" (name_of v) (pprint_index i)
  |LType i -> sprintf "TYPE %s" (pprint_index i)
  |LKind i -> sprintf "KIND %s" (pprint_index i)
  |LProd (t,tb,i) -> sprintf "((Π %s : %s . %s),%s)" (name_of (fst (unbind tb))) (pprint t) (pprint (snd (unbind (tb)))) (pprint_index i)
  |LAbst (t,tb,i) -> sprintf "((λ %s^%s : %s . %s),%s)" (name_of (fst (unbind tb))) (let vari = unbox (box_var (fst (unbind tb))) in let geti = function |LVari (_,i) -> i |_ -> failwith "not a var" in (pprint_index (geti vari))) (pprint t) (pprint (snd (unbind (tb)))) (pprint_index i)
  |LAppl (t1 ,t2, i) -> sprintf "((%s %s),%s)" (pprint t1) (pprint t2) (pprint_index i)

let labst : layered_term box -> ltbinder box -> int -> layered_term box = fun t b i -> box_apply2 (fun t b -> LAbst (t,b,i)) t b

let lvar : layered_term var -> layered_term box = fun x -> box_var x

let lapp : layered_term box -> layered_term box -> int -> layered_term box =  fun t u i -> box_apply2 (fun t u -> LAppl (t,u,i)) t u

let lprod : layered_term box -> ltbinder box -> int -> layered_term box = fun t b i -> box_apply2 (fun t b -> LProd (t,b,i)) t b

let ltype : int -> layered_term box = fun i -> box (LType i)

let lkind : int -> layered_term box = fun i -> box (LKind i)

let mkfree = fun i x -> LVari (x, i)

let renew i = i := 0

let index id ids = let o = List.assoc_opt id ids in match o with |Some i -> i |None -> dcr i;;

let rec lift_lt : layered_term -> layered_term  box = function
  |LVari (x,_) -> box_var x
  |LType i -> ltype i
  |LKind i -> lkind i
  |LAppl (t1,t2, i) -> lapp (lift_lt t1) (lift_lt t2) i
  |LProd (t1,t2,i) -> lprod (lift_lt t1) (box_binder lift_lt t2) i
  |LAbst (t1,t2,i) -> labst (lift_lt t1) (box_binder lift_lt t2) i

let rec term_to_layered_term  mapping t = match t with
  |Vari x -> let x',i = List.assoc x  mapping in LVari (x', i)
  |Type -> LType (dcr i)
  |Kind -> LKind (dcr i)
  |Prod (t1,t2) ->
    let t1' = term_to_layered_term  mapping t1 in
    let u,v = unbind t2 in
    let u' = new_var (mkfree (dcr i)) (name_of u) in
    let v' = term_to_layered_term  ((u,(u',!i))::mapping) v in
    let t2' = unbox (bind_var u' (lift_lt v')) in
    LProd (t1', t2', (dcr i))
  |Abst (t1,t2) ->
    let t1' = term_to_layered_term  mapping t1 in
    let u,v = unbind t2 in
    let u' = new_var (mkfree (dcr i)) (name_of u) in
    let v' = term_to_layered_term  ((u,(u',!i))::mapping) v in
    let t2' = unbox (bind_var u' (lift_lt v')) in
    LAbst (t1', t2', (dcr i))
  |Appl (t1,t2) -> LAppl (term_to_layered_term   mapping t1, term_to_layered_term   mapping t2, (dcr i))
  |_ -> failwith "pas marché"


let rec print_mapping = function
  |[] -> ""
  |t::q -> (sprintf "%s : %i ; " (name_of t) (uid_of t)) ^ (print_mapping q)

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
      begin
      printf "je rejoute une var";
      let x' = new_var (mkfree n) (name_of x) in
      let t' = refine ((x,x')::mapping) m n t in
      let t2' = unbox (bind_var x' (lift_lt t')) in
      LAbst (t1',t2',j)
    end
    else
      let t' = refine mapping m n t in
      let t2' = unbox (bind_var x (lift_lt t')) in
      LAbst (t1',t2',j)
  |LAppl (t1,t2,i) when i = -m -> LAppl (t1,t2,n)
  |LAppl (t1,t2,i) -> LAppl (refine mapping m n t1, refine mapping m n t2, i)
  |_ as t -> t

let layer = function
  |LVari (_,i) -> [i]
  |LType i -> [i]
  |LKind i -> [i]
  |LAppl (_,_,i) -> [i]
  |LAbst (_,_,i) -> [i]
  |LProd (_,_,i) -> [i]

let get_layer t = let f = function [] -> failwith "get_layer : liste vide" |t::_ -> t in f (layer t)

let check_layer t = match t with
  |LAppl (f,x,lapp) -> let lf,lx = get_layer f, get_layer x in if lapp = 1 then lf = 0 && lx = 0 else lf = lapp && lx <= lapp
  |LAbst (ty,b,labst) -> let _,u = unbind b in let lu, lty = get_layer u, get_layer ty in labst > 0 && lty <= labst && lu <= labst
  |LProd (ty,b,lprod) -> let _,u = unbind b in let lu, lty = get_layer u, get_layer ty in lprod > 0 && lty = lprod && lu <= lprod
  |_ -> true
