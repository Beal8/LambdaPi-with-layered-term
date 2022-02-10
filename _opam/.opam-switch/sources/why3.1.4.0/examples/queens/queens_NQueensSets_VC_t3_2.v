(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require HighOrd.
Require int.Int.
Require map.Map.
Require set.Fset.
Require set.FsetInt.
Require set.SetApp.
Require set.SetAppInt.

(* Why3 assumption *)
Inductive ref (a:Type) :=
  | ref'mk : a -> ref a.
Axiom ref_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (ref a).
Existing Instance ref_WhyType.
Arguments ref'mk {a}.

(* Why3 assumption *)
Definition contents {a:Type} {a_WT:WhyType a} (v:ref a) : a :=
  match v with
  | ref'mk x => x
  end.

Parameter n: Numbers.BinNums.Z.

(* Why3 assumption *)
Definition solution := Numbers.BinNums.Z -> Numbers.BinNums.Z.

(* Why3 assumption *)
Definition eq_prefix {a:Type} {a_WT:WhyType a} (t:Numbers.BinNums.Z -> a)
    (u:Numbers.BinNums.Z -> a) (i:Numbers.BinNums.Z) : Prop :=
  forall (k:Numbers.BinNums.Z), (0%Z <= k)%Z /\ (k < i)%Z -> ((t k) = (u k)).

(* Why3 assumption *)
Definition partial_solution (k:Numbers.BinNums.Z)
    (s:Numbers.BinNums.Z -> Numbers.BinNums.Z) : Prop :=
  forall (i:Numbers.BinNums.Z), (0%Z <= i)%Z /\ (i < k)%Z ->
  ((0%Z <= (s i))%Z /\ ((s i) < n)%Z) /\
  (forall (j:Numbers.BinNums.Z), (0%Z <= j)%Z /\ (j < i)%Z ->
   ~ ((s i) = (s j)) /\
   ~ (((s i) - (s j))%Z = (i - j)%Z) /\ ~ (((s i) - (s j))%Z = (j - i)%Z)).

Axiom partial_solution_eq_prefix :
  forall (u:Numbers.BinNums.Z -> Numbers.BinNums.Z)
    (t:Numbers.BinNums.Z -> Numbers.BinNums.Z) (k:Numbers.BinNums.Z),
  partial_solution k t -> eq_prefix t u k -> partial_solution k u.

(* Why3 assumption *)
Definition lt_sol (s1:Numbers.BinNums.Z -> Numbers.BinNums.Z)
    (s2:Numbers.BinNums.Z -> Numbers.BinNums.Z) : Prop :=
  exists i:Numbers.BinNums.Z,
  ((0%Z <= i)%Z /\ (i < n)%Z) /\ eq_prefix s1 s2 i /\ ((s1 i) < (s2 i))%Z.

(* Why3 assumption *)
Definition solutions :=
  Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z.

(* Why3 assumption *)
Definition sorted
    (s:Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z)
    (a:Numbers.BinNums.Z) (b:Numbers.BinNums.Z) : Prop :=
  forall (i:Numbers.BinNums.Z) (j:Numbers.BinNums.Z),
  (a <= i)%Z /\ (i < j)%Z /\ (j < b)%Z -> lt_sol (s i) (s j).

Axiom no_duplicate :
  forall (s:Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z)
    (a:Numbers.BinNums.Z) (b:Numbers.BinNums.Z),
  sorted s a b -> forall (i:Numbers.BinNums.Z) (j:Numbers.BinNums.Z),
  (a <= i)%Z /\ (i < j)%Z /\ (j < b)%Z -> ~ eq_prefix (s i) (s j) n.

(* Why3 goal *)
Theorem t3'vc :
  forall (col:Numbers.BinNums.Z -> Numbers.BinNums.Z) (k:Numbers.BinNums.Z)
    (sol:Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z)
    (s:Numbers.BinNums.Z) (a:set.SetAppInt.set) (b:set.SetAppInt.set)
    (c:set.SetAppInt.set),
  (0%Z <= k)%Z ->
  ((k + (set.Fset.cardinal (set.SetAppInt.to_fset a)))%Z = n) ->
  (0%Z <= s)%Z ->
  (forall (i:Numbers.BinNums.Z),
   set.Fset.mem i (set.SetAppInt.to_fset a) <->
   ((0%Z <= i)%Z /\ (i < n)%Z) /\
   (forall (j:Numbers.BinNums.Z), (0%Z <= j)%Z /\ (j < k)%Z ->
    ~ ((col j) = i))) ->
  (forall (i:Numbers.BinNums.Z), (0%Z <= i)%Z ->
   ~ set.Fset.mem i (set.SetAppInt.to_fset b) <->
   (forall (j:Numbers.BinNums.Z), (0%Z <= j)%Z /\ (j < k)%Z ->
    ~ ((col j) = ((i + j)%Z - k)%Z))) ->
  (forall (i:Numbers.BinNums.Z), (0%Z <= i)%Z ->
   ~ set.Fset.mem i (set.SetAppInt.to_fset c) <->
   (forall (j:Numbers.BinNums.Z), (0%Z <= j)%Z /\ (j < k)%Z ->
    ~ ((col j) = ((i + k)%Z - j)%Z))) ->
  partial_solution k col -> ~ set.Fset.is_empty (set.SetAppInt.to_fset a) ->
  forall (o:set.SetAppInt.set),
  ((set.SetAppInt.to_fset o) =
   (set.Fset.diff (set.SetAppInt.to_fset a) (set.SetAppInt.to_fset b))) ->
  forall (o1:set.SetAppInt.set),
  ((set.SetAppInt.to_fset o1) =
   (set.Fset.diff (set.SetAppInt.to_fset o) (set.SetAppInt.to_fset c))) ->
  (forall (u:Numbers.BinNums.Z -> Numbers.BinNums.Z),
   partial_solution n u /\ eq_prefix col u k ->
   set.Fset.mem (u k) (set.SetAppInt.to_fset o1)) ->
  forall (f:Numbers.BinNums.Z) (e:set.SetAppInt.set) (s1:Numbers.BinNums.Z)
    (sol1:Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z)
    (k1:Numbers.BinNums.Z) (col1:Numbers.BinNums.Z -> Numbers.BinNums.Z),
  (f = (s1 - s)%Z) -> (0%Z <= (s1 - s)%Z)%Z -> (k1 = k) ->
  set.Fset.subset (set.SetAppInt.to_fset e)
  (set.Fset.diff
   (set.Fset.diff (set.SetAppInt.to_fset a) (set.SetAppInt.to_fset b))
   (set.SetAppInt.to_fset c)) ->
  partial_solution k1 col1 -> sorted sol1 s s1 ->
  (forall (i:Numbers.BinNums.Z) (j:Numbers.BinNums.Z),
   set.Fset.mem i
   (set.Fset.diff (set.SetAppInt.to_fset o1) (set.SetAppInt.to_fset e)) ->
   set.Fset.mem j (set.SetAppInt.to_fset e) -> (i < j)%Z) ->
  (forall (i:Numbers.BinNums.Z), (s <= i)%Z /\ (i < s1)%Z ->
   partial_solution n (sol1 i) /\
   eq_prefix col1 (sol1 i) k1 /\
   set.Fset.mem (sol1 i k1)
   (set.Fset.diff (set.SetAppInt.to_fset o1) (set.SetAppInt.to_fset e))) ->
  (forall (t:Numbers.BinNums.Z -> Numbers.BinNums.Z),
   partial_solution n t /\
   eq_prefix col1 t k1 /\
   set.Fset.mem (t k1)
   (set.Fset.diff (set.SetAppInt.to_fset o1) (set.SetAppInt.to_fset e)) ->
   set.Fset.mem (t k1) (set.SetAppInt.to_fset o1) /\
   ~ set.Fset.mem (t k1) (set.SetAppInt.to_fset e) /\
   (exists i:Numbers.BinNums.Z,
    ((s <= i)%Z /\ (i < s1)%Z) /\ eq_prefix t (sol1 i) n)) ->
  eq_prefix col col1 k1 -> eq_prefix sol sol1 s ->
  ~ set.Fset.is_empty (set.SetAppInt.to_fset e) ->
  let d := set.FsetInt.min_elt (set.SetAppInt.to_fset e) in
  forall (col2:Numbers.BinNums.Z -> Numbers.BinNums.Z),
  (col2 = (map.Map.set col1 k1 d)) -> forall (k2:Numbers.BinNums.Z),
  (k2 = (k1 + 1%Z)%Z) -> forall (o2:set.SetAppInt.set),
  ((set.SetAppInt.to_fset o2) = (set.Fset.add d (set.SetAppInt.to_fset c))) ->
  set.Fset.mem d (set.SetAppInt.to_fset c) /\
  ((set.Fset.cardinal (set.SetAppInt.to_fset o2)) =
   (set.Fset.cardinal (set.SetAppInt.to_fset c))) \/
  ~ set.Fset.mem d (set.SetAppInt.to_fset c) /\
  ((set.Fset.cardinal (set.SetAppInt.to_fset o2)) =
   ((set.Fset.cardinal (set.SetAppInt.to_fset c)) + 1%Z)%Z) ->
  forall (o3:set.SetAppInt.set),
  (forall (i:Numbers.BinNums.Z),
   set.Fset.mem i (set.SetAppInt.to_fset o3) <->
   (0%Z <= i)%Z /\ set.Fset.mem (i + 1%Z)%Z (set.SetAppInt.to_fset o2)) ->
  forall (o4:set.SetAppInt.set),
  ((set.SetAppInt.to_fset o4) = (set.Fset.add d (set.SetAppInt.to_fset b))) ->
  set.Fset.mem d (set.SetAppInt.to_fset b) /\
  ((set.Fset.cardinal (set.SetAppInt.to_fset o4)) =
   (set.Fset.cardinal (set.SetAppInt.to_fset b))) \/
  ~ set.Fset.mem d (set.SetAppInt.to_fset b) /\
  ((set.Fset.cardinal (set.SetAppInt.to_fset o4)) =
   ((set.Fset.cardinal (set.SetAppInt.to_fset b)) + 1%Z)%Z) ->
  forall (o5:set.SetAppInt.set),
  (forall (i:Numbers.BinNums.Z),
   set.Fset.mem i (set.SetAppInt.to_fset o5) <->
   (1%Z <= i)%Z /\ set.Fset.mem (i - 1%Z)%Z (set.SetAppInt.to_fset o4)) ->
  forall (o6:set.SetAppInt.set),
  ((set.SetAppInt.to_fset o6) =
   (set.Fset.remove d (set.SetAppInt.to_fset a))) ->
  set.Fset.mem d (set.SetAppInt.to_fset a) /\
  ((set.Fset.cardinal (set.SetAppInt.to_fset o6)) =
   ((set.Fset.cardinal (set.SetAppInt.to_fset a)) - 1%Z)%Z) \/
  ~ set.Fset.mem d (set.SetAppInt.to_fset a) /\
  ((set.Fset.cardinal (set.SetAppInt.to_fset o6)) =
   (set.Fset.cardinal (set.SetAppInt.to_fset a))) ->
  forall (s2:Numbers.BinNums.Z)
    (sol2:Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z)
    (k3:Numbers.BinNums.Z) (col3:Numbers.BinNums.Z -> Numbers.BinNums.Z),
  (0%Z <= (s2 - s1)%Z)%Z -> (k3 = k2) -> sorted sol2 s1 s2 ->
  (forall (t:Numbers.BinNums.Z -> Numbers.BinNums.Z),
   partial_solution n t /\ eq_prefix col3 t k3 <->
   (exists i:Numbers.BinNums.Z,
    ((s1 <= i)%Z /\ (i < s2)%Z) /\ eq_prefix t (sol2 i) n)) ->
  eq_prefix col2 col3 k3 -> eq_prefix sol1 sol2 s1 ->
  forall (f1:Numbers.BinNums.Z), (f1 = (f + (s2 - s1)%Z)%Z) ->
  forall (k4:Numbers.BinNums.Z), (k4 = (k3 - 1%Z)%Z) ->
  forall (e1:set.SetAppInt.set),
  ((set.SetAppInt.to_fset e1) =
   (set.Fset.remove d (set.SetAppInt.to_fset e))) ->
  set.Fset.mem d (set.SetAppInt.to_fset e) /\
  ((set.Fset.cardinal (set.SetAppInt.to_fset e1)) =
   ((set.Fset.cardinal (set.SetAppInt.to_fset e)) - 1%Z)%Z) \/
  ~ set.Fset.mem d (set.SetAppInt.to_fset e) /\
  ((set.Fset.cardinal (set.SetAppInt.to_fset e1)) =
   (set.Fset.cardinal (set.SetAppInt.to_fset e))) ->
  sorted sol2 s s2.
(* Why3 intros col k sol s a b c h1 h2 h3 h4 h5 h6 h7 h8 o h9 o1 h10 h11 f e
        s1 sol1 k1 col1 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 d
        col2 h24 k2 h25 o2 h26 h27 o3 h28 o4 h29 h30 o5 h31 o6 h32 h33 s2
        sol2 k3 col3 h34 h35 h36 h37 h38 h39 f1 h40 k4 h41 e1 h42 h43. *)
Proof.
intros col k sol s a b c h1 h2 h3 h4 h5 h6 h7 h8 o h9 o1 h10 h11 f e
        s1 sol1 k1 col1 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 d
        col2 h24 k2 h25 o2 h26 h27 o3 h28 o4 h29 h30 o5 h31 o6 h32 h33 s2
        sol2 k3 col3 h34 h35 h36 h37 h38 h39 f1 h40 k4 h41 e1 h42 h43.
red; intros i j hij.
assert (case: (j < s1 \/ s1 <= j)%Z) by omega. destruct case.
do 2 (rewrite <- h39; try omega).
apply h17; omega.
assert (case: (s1 <= i \/ i < s1)%Z) by omega. destruct case.
apply h36; omega.
(* s1 <= i < s2 <= j < s3 *)
red.
subst k1. (* rename k1 into k.*)
assert (k < n)%Z.
generalize (Fset.cardinal_nonneg (SetAppInt.to_fset a)).
generalize (Fset.cardinal_empty (SetAppInt.to_fset a)).
intros.
assert (case: (Fset.cardinal (SetAppInt.to_fset a) = 0 \/ 
              Fset.cardinal (SetAppInt.to_fset a) > 0)%Z) by omega. destruct case.
absurd (Fset.is_empty (SetAppInt.to_fset a)). auto. intuition.
omega.

assert (ha: eq_prefix col1 (sol1 i) k /\ 
       Fset.mem (sol1 i k) (Fset.diff (SetAppInt.to_fset o1) (SetAppInt.to_fset e))).
  apply (h19 i).
  omega.
destruct ha as (ha,hb).

destruct (h37 (sol2 j)) as (_,hj).
destruct hj.
exists j.
split.
intuition.
red; intuition.
clear h36.

exists k.
split. intuition.
(* eq_prefix ... *)
rewrite <- h39; try omega.
split.
red; intros l hl.
rewrite <- H3; try omega.
rewrite <- h38; try omega.
subst col2.
generalize (Map.set'def col1 k d l).
intros (_,h).
rewrite h.
rewrite <- ha; omega.
omega.
(* s[i][k] < s[j][k] *)
apply h18.
rewrite <- h39; try omega.
auto.
rewrite <- H3; try omega.
rewrite <- h38; try omega.
subst col2.
generalize (Map.set'def col1 k d k).
intros (h,_).
rewrite h; try omega.
generalize (set.FsetInt.min_elt_def (SetAppInt.to_fset e)); intuition.
Qed.
