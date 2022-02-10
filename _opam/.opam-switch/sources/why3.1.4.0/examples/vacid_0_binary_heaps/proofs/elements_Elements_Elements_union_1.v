(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require HighOrd.
Require int.Int.
Require int.MinMax.
Require map.Map.

Axiom bag : forall (a:Type), Type.
Parameter bag_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (bag a).
Existing Instance bag_WhyType.

Parameter nb_occ: forall {a:Type} {a_WT:WhyType a}, a -> (bag a) -> Z.

Axiom occ_non_negative :
  forall {a:Type} {a_WT:WhyType a},
  forall (b:bag a) (x:a), (0%Z <= (nb_occ x b))%Z.

(* Why3 assumption *)
Definition mem {a:Type} {a_WT:WhyType a} (x:a) (b:bag a) : Prop :=
  (0%Z < (nb_occ x b))%Z.

(* Why3 assumption *)
Definition eq_bag {a:Type} {a_WT:WhyType a} (a1:bag a) (b:bag a) : Prop :=
  forall (x:a), ((nb_occ x a1) = (nb_occ x b)).

Axiom bag_extensionality :
  forall {a:Type} {a_WT:WhyType a},
  forall (a1:bag a) (b:bag a), (eq_bag a1 b) -> (a1 = b).

Parameter empty_bag: forall {a:Type} {a_WT:WhyType a}, bag a.

Axiom occ_empty :
  forall {a:Type} {a_WT:WhyType a},
  forall (x:a), ((nb_occ x (empty_bag : bag a)) = 0%Z).

Axiom is_empty :
  forall {a:Type} {a_WT:WhyType a},
  forall (b:bag a), (forall (x:a), ((nb_occ x b) = 0%Z)) ->
  (b = (empty_bag : bag a)).

Parameter singleton: forall {a:Type} {a_WT:WhyType a}, a -> bag a.

Axiom occ_singleton :
  forall {a:Type} {a_WT:WhyType a},
  forall (x:a) (y:a),
  ((x = y) /\ ((nb_occ y (singleton x)) = 1%Z)) \/
  (~ (x = y) /\ ((nb_occ y (singleton x)) = 0%Z)).

Axiom occ_singleton_eq :
  forall {a:Type} {a_WT:WhyType a},
  forall (x:a) (y:a), (x = y) -> ((nb_occ y (singleton x)) = 1%Z).

Axiom occ_singleton_neq :
  forall {a:Type} {a_WT:WhyType a},
  forall (x:a) (y:a), ~ (x = y) -> ((nb_occ y (singleton x)) = 0%Z).

Parameter union:
  forall {a:Type} {a_WT:WhyType a}, (bag a) -> (bag a) -> bag a.

Axiom occ_union :
  forall {a:Type} {a_WT:WhyType a},
  forall (x:a) (a1:bag a) (b:bag a),
  ((nb_occ x (union a1 b)) = ((nb_occ x a1) + (nb_occ x b))%Z).

Axiom Union_comm :
  forall {a:Type} {a_WT:WhyType a},
  forall (a1:bag a) (b:bag a), ((union a1 b) = (union b a1)).

Axiom Union_identity :
  forall {a:Type} {a_WT:WhyType a},
  forall (a1:bag a), ((union a1 (empty_bag : bag a)) = a1).

Axiom Union_assoc :
  forall {a:Type} {a_WT:WhyType a},
  forall (a1:bag a) (b:bag a) (c:bag a),
  ((union a1 (union b c)) = (union (union a1 b) c)).

Axiom bag_simpl_right :
  forall {a:Type} {a_WT:WhyType a},
  forall (a1:bag a) (b:bag a) (c:bag a), ((union a1 b) = (union c b)) ->
  (a1 = c).

Axiom bag_simpl_left :
  forall {a:Type} {a_WT:WhyType a},
  forall (a1:bag a) (b:bag a) (c:bag a), ((union a1 b) = (union a1 c)) ->
  (b = c).

(* Why3 assumption *)
Definition add {a:Type} {a_WT:WhyType a} (x:a) (b:bag a) : bag a :=
  union (singleton x) b.

Axiom occ_add_eq :
  forall {a:Type} {a_WT:WhyType a},
  forall (b:bag a) (x:a) (y:a), (x = y) ->
  ((nb_occ y (add x b)) = ((nb_occ y b) + 1%Z)%Z).

Axiom occ_add_neq :
  forall {a:Type} {a_WT:WhyType a},
  forall (b:bag a) (x:a) (y:a), ~ (x = y) ->
  ((nb_occ y (add x b)) = (nb_occ y b)).

Parameter card: forall {a:Type} {a_WT:WhyType a}, (bag a) -> Z.

Axiom Card_nonneg :
  forall {a:Type} {a_WT:WhyType a}, forall (x:bag a), (0%Z <= (card x))%Z.

Axiom Card_empty :
  forall {a:Type} {a_WT:WhyType a}, ((card (empty_bag : bag a)) = 0%Z).

Axiom Card_zero_empty :
  forall {a:Type} {a_WT:WhyType a},
  forall (x:bag a), ((card x) = 0%Z) -> (x = (empty_bag : bag a)).

Axiom Card_singleton :
  forall {a:Type} {a_WT:WhyType a},
  forall (x:a), ((card (singleton x)) = 1%Z).

Axiom Card_union :
  forall {a:Type} {a_WT:WhyType a},
  forall (x:bag a) (y:bag a), ((card (union x y)) = ((card x) + (card y))%Z).

Axiom Card_add :
  forall {a:Type} {a_WT:WhyType a},
  forall (x:a) (b:bag a), ((card (add x b)) = (1%Z + (card b))%Z).

Parameter diff:
  forall {a:Type} {a_WT:WhyType a}, (bag a) -> (bag a) -> bag a.

Axiom Diff_occ :
  forall {a:Type} {a_WT:WhyType a},
  forall (b1:bag a) (b2:bag a) (x:a),
  ((nb_occ x (diff b1 b2)) =
   (ZArith.BinInt.Z.max 0%Z ((nb_occ x b1) - (nb_occ x b2))%Z)).

Axiom Diff_empty_right :
  forall {a:Type} {a_WT:WhyType a},
  forall (b:bag a), ((diff b (empty_bag : bag a)) = b).

Axiom Diff_empty_left :
  forall {a:Type} {a_WT:WhyType a},
  forall (b:bag a), ((diff (empty_bag : bag a) b) = (empty_bag : bag a)).

Axiom Diff_add :
  forall {a:Type} {a_WT:WhyType a},
  forall (b:bag a) (x:a), ((diff (add x b) (singleton x)) = b).

Axiom Diff_comm :
  forall {a:Type} {a_WT:WhyType a},
  forall (b:bag a) (b1:bag a) (b2:bag a),
  ((diff (diff b b1) b2) = (diff (diff b b2) b1)).

Axiom Add_diff :
  forall {a:Type} {a_WT:WhyType a},
  forall (b:bag a) (x:a), (mem x b) -> ((add x (diff b (singleton x))) = b).

Parameter choose: forall {a:Type} {a_WT:WhyType a}, (bag a) -> a.

Axiom choose_mem :
  forall {a:Type} {a_WT:WhyType a},
  forall (b:bag a), ~ ((empty_bag : bag a) = b) -> mem (choose b) b.

(* Why3 assumption *)
Definition array (a:Type) := Z -> a.

Parameter elements:
  forall {a:Type} {a_WT:WhyType a}, (Z -> a) -> Z -> Z -> bag a.

Axiom Elements_empty :
  forall {a:Type} {a_WT:WhyType a},
  forall (a1:Z -> a) (i:Z) (j:Z), (j <= i)%Z ->
  ((elements a1 i j) = (empty_bag : bag a)).

Axiom Elements_add :
  forall {a:Type} {a_WT:WhyType a},
  forall (a1:Z -> a) (i:Z) (j:Z), (i < j)%Z ->
  ((elements a1 i j) = (add (a1 (j - 1%Z)%Z) (elements a1 i (j - 1%Z)%Z))).

Axiom Elements_singleton :
  forall {a:Type} {a_WT:WhyType a},
  forall (a1:Z -> a) (i:Z) (j:Z), (j = (i + 1%Z)%Z) ->
  ((elements a1 i j) = (singleton (a1 i))).

(* Why3 goal *)
Theorem Elements_union {a:Type} {a_WT:WhyType a} :
  forall (a1:Z -> a) (i:Z) (j:Z) (k:Z), ((i <= j)%Z /\ (j <= k)%Z) ->
  ((elements a1 i k) = (union (elements a1 i j) (elements a1 j k))).
Proof.
intros a1 i j k (h1,h2).
apply Zlt_lower_bound_ind with (z := j)
     (P := fun k => elements a1 i k = union (elements a1 i j) (elements a1 j k)); auto.
intros x H_ind H.
assert (h: (j = x \/ j < x)%Z) by omega.
  destruct h.
  (*  j = x *)
  subst x.
   rewrite (Elements_empty _ j); auto.
   rewrite Union_identity; auto.
   (* j < x *)
   rewrite (Elements_add _ j); auto.
   rewrite (Elements_add _ i); auto with zarith.
   unfold add.
   rewrite H_ind with (y := (x - 1)%Z); auto with zarith.
   apply bag_extensionality.
   intro z.
   repeat rewrite occ_union; auto with zarith.
Qed.

