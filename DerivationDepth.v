Require Import List.
Import ListNotations.
Require Import ListFacts.
Require Import Arith.
Require Import Formula.
Require Import FormulaFacts.

Require Import UserTactics.

From Coq Require Import ssreflect ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Wf_nat.
Require Import Psatz.



(*iipc2 derivations containing derivation depth without regard for well-formedness*)
Inductive derivation_depth : nat -> list formula -> formula -> Prop :=
  | dd_ax : forall (d : nat) (Gamma: list formula) (s: formula), In s Gamma -> derivation_depth d Gamma s
  | dd_elim_arr : forall (d: nat) (Gamma: list formula) (s t: formula), derivation_depth d Gamma (Formula.arr s t) -> derivation_depth d Gamma s -> derivation_depth (1+d) Gamma t
  | dd_intro_arr : forall (d: nat) (Gamma: list formula) (s t : formula), derivation_depth d (s :: Gamma) t -> derivation_depth (1+d) Gamma (Formula.arr s t)
  | dd_elim_quant : forall (d: nat) (Gamma: list formula) (s t : formula), derivation_depth d Gamma (Formula.quant s) -> well_formed_formula t -> derivation_depth (1+d) Gamma (instantiate t 0 s)
  | dd_intro_quant : forall (d: nat) (Gamma: list formula) (s: formula), 
      (forall (a: label), derivation_depth d Gamma (instantiate (atom a) 0 s)) -> derivation_depth (1+d) Gamma (Formula.quant s).

Lemma derivation_depth_relax : forall d d' Gamma t, derivation_depth d Gamma t -> d <= d' -> derivation_depth d' Gamma t.
Proof.
elim.
intros *. inversion => ?. by apply : dd_ax.

move => d IH. intros *. inversion => ?.
all: have -> : d' = 1+(d'-1) by lia.
all: have ? : d <= (d'-1) by lia.

by apply : dd_ax.
apply : dd_elim_arr; by eauto.
apply : dd_intro_arr; by auto.
apply : dd_elim_quant; by auto.
apply : dd_intro_quant; by auto.
Qed.


Lemma substitute_label_derivation_depth : forall d (a b: label) Gamma t, derivation_depth d Gamma t -> derivation_depth d (map (substitute_label a b) Gamma) (substitute_label a b t).
Proof.
elim.
intros *. inversion. apply : dd_ax. by apply /in_map.
move => d IH a b Gamma ?. inversion => /=.

apply : dd_ax. by apply /in_map.

apply : dd_elim_arr; eauto.
have <- : forall s t, substitute_label a b (Formula.arr s t) = Formula.arr (substitute_label a b s) (substitute_label a b t) by intros; reflexivity.
by auto.

apply : dd_intro_arr. rewrite -map_cons. by auto.

rewrite -substitute_instantiation. apply : dd_elim_quant.
have -> : forall s, (quant (substitute_label a b s)) = substitute_label a b (quant s) by reflexivity.
by eauto. by apply : lc_substitute.

apply : dd_intro_quant => c.

case : (Label.eq_dec c a) => ?.
subst.
have [c' ?] := exists_fresh ([Formula.atom a; Formula.atom b; s] ++ (map (substitute_label a b) Gamma)).
do 3 (grab Forall; inversion).

do 2 (grab shape (fresh_in c' (atom _)); inversion).
rewrite (@instantiate_renaming_eq _ _ _ c') => //.
rewrite (@map_substitute_fresh_label c' a (map (substitute_label a b) Gamma)); by auto.

rewrite instantiate_renaming_neq; by auto.
Qed.


Module InstantiateAll.

Fixpoint instantiate_all (n : nat) (t : formula) : formula :=
  match t with
  | Formula.var m => if n <=? m then Formula.atom (0,0) else t
  | Formula.atom _ => t
  | Formula.arr s t => Formula.arr (instantiate_all n s) (instantiate_all n t)
  | Formula.quant s => Formula.quant (instantiate_all (1+n) s)
  end.


Lemma lc_instantiate_all : forall t n, lc n t -> instantiate_all n t = t.
Proof.
elim => /=.
intros *. inversion. by inspect_eqb.
by auto.
move => *. grab lc. inversion. f_equal; by auto.
move => *. grab lc. inversion. f_equal; by auto.
Qed.

Lemma lc_map_instantiate_all : forall Gamma, Forall well_formed_formula Gamma -> map (instantiate_all 0) Gamma = Gamma.
Proof.
elim => //=.
move => ? ? ? /Forall_cons_iff => [[? ?]].
f_equal; auto.
by apply lc_instantiate_all.
Qed.

Lemma instantiate_all_lc : forall t n, lc n (instantiate_all n t).
Proof.
elim => /=.
move => m n.
have : (n <= m) \/ (m < n) by lia.
case => ?; inspect_eqb; by constructor.
move => *. by constructor.
move => *. constructor; by auto.
move => *. constructor; by auto.
Qed.


Lemma instantiate_all_instantiate : forall t, well_formed_formula t -> forall s n, (instantiate_all n (instantiate t n s)) = instantiate t n (instantiate_all (1+n) s).
Proof.
move => t ?.
elim.

move => m n.
have : (n = m) \/ (n < m) \/ (n > m) by lia.
(case; last case) => ?.
1-3: rewrite /instantiate -/instantiate /instantiate_all -/instantiate_all; do ? inspect_eqb.
1-3: rewrite /instantiate -/instantiate /instantiate_all -/instantiate_all; do ? inspect_eqb => //.
rewrite lc_instantiate_all => //.
apply: Lc.relax; first eassumption. by lia.

by auto.

all: move => /=.
move => *. f_equal; auto.
move => *. f_equal; auto.
Qed.


Lemma instantiate_all_derivation_depth : forall d Gamma t, derivation_depth d Gamma t -> derivation_depth d (map (instantiate_all 0) Gamma) (instantiate_all 0 t).
Proof.
elim.
move => *. grab derivation_depth. inversion. apply : dd_ax.
by apply in_map.

move => d IH ? ?. inversion => /=.

apply : dd_ax. by apply in_map.

grab derivation_depth. move /IH => ?.
apply : dd_elim_arr; eauto.
have <- : forall n s t, instantiate_all n (Formula.arr s t) = Formula.arr (instantiate_all n s) (instantiate_all n t) by intros; reflexivity.
by auto.

apply : dd_intro_arr.
rewrite -map_cons. by eauto.

rewrite instantiate_all_instantiate. done.
apply : dd_elim_quant; eauto.
have -> : (quant (instantiate_all 1 s)) = instantiate_all 0 (quant s) by reflexivity.
by eauto.

apply : dd_intro_quant => a.
rewrite -instantiate_all_instantiate. by constructor.
by eauto.
Qed.

End InstantiateAll.
