(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.

(* Why3 assumption *)
Inductive t (a:Type) :=
  | T : a -> t a.
Axiom t_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (t a).
Existing Instance t_WhyType.
Implicit Arguments T [[a]].

(* Why3 assumption *)
Inductive u (a:Type) :=
  | U1 : (t (u a)) -> u a
  | U2 : u a.
Axiom u_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (u a).
Existing Instance u_WhyType.
Implicit Arguments U1 [[a]].
Implicit Arguments U2 [[a]].

Parameter f: forall {a:Type} {a_WT:WhyType a}, a.

(* Why3 assumption *)
Inductive v {a:Type} {a_WT:WhyType a}: (u a) -> Prop :=
  | v1 : forall (c:(u a)), (v (U1 (T c)))
  | v2 : (v (f : (u a))).

Parameter id: forall {a:Type} {a_WT:WhyType a}, a -> a.

Axiom ax : forall {a:Type} {a_WT:WhyType a}, forall (x:a), ((id x) = x).

(* Why3 goal *)
Theorem g1 : forall {a:Type} {a_WT:WhyType a}, exists x:a, ((id x) = x).
Proof.
exists why_inhabitant.
apply ax.
Qed.
