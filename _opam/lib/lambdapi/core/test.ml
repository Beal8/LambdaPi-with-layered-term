open Bindlib

type tbinder = (test , test) binder

and test = Var of test var | Abst of tbinder

let mkfree = fun x -> Var x

let t = let x = new_var mkfree "x" in let b = box_var x in let bind = bind_var x b in Abst (unbox bind)
