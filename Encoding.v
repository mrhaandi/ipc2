Load Common.

Require Import FormulaFacts.
Require Import Psatz. (*lia : linear integer arithmetic*)
Require Import Derivations.
Require Import Diophantine.
Require Import UserTactics.

Definition dagger : formula := atom (0, 0).
Definition triangle : formula := atom (0, 1).
Definition to_dagger (s: formula) := arr s dagger.

Definition bullet1 : formula := atom (2, 1).
Definition bullet2 : formula := atom (2, 2).
Definition bullet3 : formula := atom (2, 3).
Definition a_u : formula := atom (3, 1).
Definition a_s : formula := atom (3, 2).
Definition a_p : formula := atom (3, 3).

Definition represent_nat (n : nat) : formula := atom (1, n).
Definition one : formula := represent_nat 1. (*number encoding: [atom (1,n)] = n*)

Definition U (s: formula) := arr (arr (to_dagger s) bullet1) (arr (arr s bullet2) a_u).
Definition S (s t u: formula) := 
    arr (arr (to_dagger s) bullet1) 
        (arr (arr (to_dagger t) bullet2) 
            (arr (arr (to_dagger u) bullet3) a_s)).
Definition P (s t u: formula) := 
    arr (arr (to_dagger s) bullet1) 
        (arr (arr (to_dagger t) bullet2) 
            (arr (arr (to_dagger u) bullet3) a_p)).

Definition calC : list formula := [a_u; a_s; a_p; triangle; bullet1; bullet2; bullet3].

Inductive interpretation (s : formula) (n : nat) : Prop :=
  | interpret :
    derivation calC (Formula.arr (to_dagger s) (to_dagger (represent_nat n))) ->
    derivation calC (Formula.arr (to_dagger (represent_nat n)) (to_dagger s)) -> interpretation s n.

Lemma interpretation_of_representation : forall (n: nat), interpretation (represent_nat n) n.
Proof.
split; apply intro_arr; derivation_rule.
Qed. 

Lemma interpretation_one : interpretation one 1.
Proof.
split; apply intro_arr; derivation_rule.
Qed.

Definition s_x_u : formula := let a := 1 in let b := 0 in
    quant (
    arr (U (var 0)) (arr ( quant ( arr (U (var b)) (
    arr (S (var a) one (var b)) ( arr (P (var b) one (var b)) triangle)))) triangle)).

Definition s_x_s : formula := let a := 4 in let b := 3 in let c := 2 in let d := 1 in let e := 0 in
    quant ( quant ( quant ( quant ( quant ( 
    arr (U (var a)) ( arr (U (var b)) ( arr (U (var c)) ( arr (U (var d)) ( arr (U (var e)) (
    arr (S (var a) (var b) (var c)) ( arr (S (var b) one (var d)) ( arr (S (var c) one (var e)) ( 
    arr (arr (S (var a) (var d) (var e)) triangle) triangle))))))))))))).

Definition s_x_p : formula := let a := 4 in let b := 3 in let c := 2 in let d := 1 in let e := 0 in
    quant ( quant ( quant ( quant ( quant ( 
    arr (U (var a)) ( arr (U (var b)) ( arr (U (var c)) ( arr (U (var d)) ( arr (U (var e)) (
    arr (P (var a) (var b) (var c)) ( arr (S (var b) one (var d)) ( arr (S (var c) (var a) (var e)) ( 
    arr (arr (P (var a) (var d) (var e)) triangle) triangle))))))))))))).

Definition represent_diophantine (d : diophantine) (t : formula) : formula :=
  match d with
  | dio_one a => arr (U (var a)) (arr (P (var a) (var a) one) t)
  | dio_sum a b c => arr (U (var a)) (arr (U (var b)) (arr (U (var c)) (arr (S (var a) (var b) (var c)) t)))
  | dio_prod a b c => arr (U (var a)) (arr (U (var b)) (arr (U (var c)) (arr (P (var a) (var b) (var c)) t)))
  end.

Fixpoint represent_diophantines (ds : list diophantine) : formula :=
  match ds with 
  | [] => triangle 
  | d :: ds' => represent_diophantine d (represent_diophantines ds')
  end.

Fixpoint diophantine_variable_bound (ds : list diophantine) : nat :=
  match ds with
  | [] => 0
  | (dio_one x) :: ds => max (diophantine_variable_bound ds) (1 + x)
  | (dio_sum x y z) :: ds => max (diophantine_variable_bound ds) (max (1 + x) (max (1 + y) (1 + z)))
  | (dio_prod x y z) :: ds => max (diophantine_variable_bound ds) (max (1 + x) (max (1 + y) (1 + z)))
  end.

Definition s_x_d (ds : list diophantine) := let n := diophantine_variable_bound ds in
  quantify_formula n (arr (arr triangle triangle) (represent_diophantines ds)).

Definition ΓI (ds : list diophantine) := [s_x_s; s_x_u; s_x_p; s_x_d ds].

(*we consider encoding of strictly positive natural numbers*)
Definition represents_nat (s : formula) := exists (m : nat), 
  s = U (represent_nat m) /\ m > 0.

Definition encodes_nat (s : formula) := exists (m1 : nat) (s1 : formula), 
  s = U s1 /\ interpretation s1 m1.

Definition encodes_sum (s : formula) := exists (s1 s2 s3 : formula), 
  s = S s1 s2 s3 /\ (exists (m1 m2 m3 : nat), interpretation s1 m1 /\ interpretation s2 m2 /\ interpretation s3 m3 /\ m1 + m2 = m3).

Definition encodes_prod (s : formula) := exists (s1 s2 s3 : formula), 
  s = P s1 s2 s3 /\ (exists (m1 m2 m3 : nat), interpretation s1 m1 /\ interpretation s2 m2 /\ interpretation s3 m3 /\ m1 * m2 = m3).

Definition represent_diophantine_repr (f : nat -> formula) (d : diophantine) : list formula :=
  match d with
  | dio_one a => [U (f a); P (f a) (f a) one]
  | dio_sum a b c => [U (f a); U (f b); U (f c); S (f a) (f b) (f c)]
  | dio_prod a b c => [U (f a); U (f b); U (f c); P (f a) (f b) (f c)]
  end.


Lemma lc_represent_diophantines : forall ds, lc (diophantine_variable_bound ds) (represent_diophantines ds).
Proof.
elim.
constructor.
case; (
  intros; simpl;
  do ? (try lia; constructor);
  eapply Lc.relax; [ eassumption | lia ]).
Qed.


Ltac decompose_lc := 
  do ? (
  match goal with
  | [H : lc _ ?s |- _] => 
    match eval hnf in s with
    | arr _ _ => inversion_clear H
    | var _ => inversion_clear H
    | atom _ => inversion_clear H
    end
  end).

Lemma inspect_chain_diophantines_aux_one : forall (m : nat) (params : list formula) (ds : list diophantine), 
  lc m (represent_diophantines ds) ->
  chain (quantify_formula m (arr (arr triangle triangle) (represent_diophantines ds))) (get_label triangle) params -> 
  exists (f : nat -> formula), 
  tail params = flat_map (represent_diophantine_repr f) ds /\ (forall (x : nat), m <= x -> f x = one).
Proof.
(*no more induction on n*)
intros.
gimme chain; simpl; inversion.
gimme contains. simpl.

move /quantified_arrow_not_contains_atom => //.

gimme contains; move /contains_to_prenex_instantiation.
gimme lc => H_lc.
move /(_ H_lc) => [f [? [H_f H_f2]]].

exists (fun n => match f n with | Some u => u | _ => one end); simpl.
split.

revert dependent ts.
revert dependent u.
revert dependent ds.
elim.
(*no equations*)
simpl.
intros; subst.
gimme chain; inversion; auto.
gimme contains; inversion.
(*at least one equation*)


case.
{
move => x.
simpl. intros * => IH; intros; subst.
decompose_chain.
decompose_lc.
compute.
have : exists u, f x = Some u ∧ lc 0 u by auto.
move => [? [-> ?]].
do ? f_equal.
apply : IH => //.
}

{
move => x y z.
simpl. intros * => IH; intros; subst.
decompose_chain.
decompose_lc.
compute.
have : exists ux, f x = Some ux ∧ lc 0 ux by auto.
have : exists uy, f y = Some uy ∧ lc 0 uy by auto.
have : exists uz, f z = Some uz ∧ lc 0 uz by auto.
move => [? [-> ?]] [? [-> ?]] [? [-> ?]].
do ? f_equal.
apply : IH => //.
}

{
move => x y z.
simpl. intros * => IH; intros; subst.
decompose_chain.
decompose_lc.
compute.
have : exists ux, f x = Some ux ∧ lc 0 ux by auto.
have : exists uy, f y = Some uy ∧ lc 0 uy by auto.
have : exists uz, f z = Some uz ∧ lc 0 uz by auto.
move => [? [-> ?]] [? [-> ?]] [? [-> ?]].
do ? f_equal.
apply : IH => //.
}

move => x Hx.
have : f x = None by auto.
by move => ->.
Qed.


Lemma inspect_chain_diophantines_aux : forall (m : nat) (params : list formula) (ds : list diophantine), 
  lc m (represent_diophantines ds) ->
  chain (quantify_formula m (arr (arr triangle triangle) (represent_diophantines ds))) (get_label triangle) params -> 
  exists (f : nat -> formula), 
  tail params = flat_map (represent_diophantine_repr f) ds.
Proof.
(*no more induction on n*)
intros.
gimme chain; simpl; inversion.
gimme contains. simpl.

move /quantified_arrow_not_contains_atom => //.

gimme contains; move /contains_to_prenex_instantiation.
gimme lc => H_lc.
move /(_ H_lc) => [f [? [H_f ?]]].

exists (fun n => match f n with | Some u => u | _ => one end); simpl.

revert dependent ts.
revert dependent u.
revert dependent ds.
elim.
(*no equations*)
simpl.
intros; subst.
gimme chain; inversion; auto.
gimme contains; inversion.
(*at least one equation*)


case.
{
move => x.
simpl. intros * => IH; intros; subst.
decompose_chain.
decompose_lc.
compute.
have : exists u, f x = Some u ∧ lc 0 u by auto.
move => [? [-> ?]].
do ? f_equal.
apply : IH => //.
}

{
move => x y z.
simpl. intros * => IH; intros; subst.
decompose_chain.
decompose_lc.
compute.
have : exists ux, f x = Some ux ∧ lc 0 ux by auto.
have : exists uy, f y = Some uy ∧ lc 0 uy by auto.
have : exists uz, f z = Some uz ∧ lc 0 uz by auto.
move => [? [-> ?]] [? [-> ?]] [? [-> ?]].
do ? f_equal.
apply : IH => //.
}

{
move => x y z.
simpl. intros * => IH; intros; subst.
decompose_chain.
decompose_lc.
compute.
have : exists ux, f x = Some ux ∧ lc 0 ux by auto.
have : exists uy, f y = Some uy ∧ lc 0 uy by auto.
have : exists uz, f z = Some uz ∧ lc 0 uz by auto.
move => [? [-> ?]] [? [-> ?]] [? [-> ?]].
do ? f_equal.
apply : IH => //.
}
Qed.


Lemma inspect_chain_diophantines : forall (params : list formula) (ds : list diophantine), 
  chain (s_x_d ds) (get_label triangle) params -> 
  exists (f : nat -> formula), 
  tail params = flat_map (represent_diophantine_repr f) ds.
Proof.
eauto using inspect_chain_diophantines_aux, lc_represent_diophantines.
Qed.

Lemma inspect_chain_diophantines_one : forall (params : list formula) (ds : list diophantine), 
  chain (s_x_d ds) (get_label triangle) params -> 
  exists (f : nat -> formula), 
  tail params = flat_map (represent_diophantine_repr f) ds /\ (forall (x : nat), diophantine_variable_bound ds <= x -> f x = one).
Proof.
eauto using inspect_chain_diophantines_aux_one, lc_represent_diophantines.
Qed.

(*HintDb containing instantiation simplification rules*)
Create HintDb simplify_formula.
Lemma simplify_instantiate_arrow : forall s t u n, instantiate s n (arr t u) = arr (instantiate s n t) (instantiate s n u).
Proof. reflexivity. Qed. 
Lemma simplify_instantiate_var_eq : forall s n m, n = m -> instantiate s n (var m) = s.
Proof. intros *. move => ->. unfold instantiate. inspect_eqb. reflexivity. Qed.
Lemma simplify_instantiate_var_neq : forall s n m, n <> m -> instantiate s n (var m) = var m.
Proof. intros *. move => ?. unfold instantiate. inspect_eqb. reflexivity. Qed.
Lemma simplify_instantiate_quant : forall s n t, instantiate s n (quant t) = quant (instantiate s (1+n) t).
Proof. reflexivity. Qed.
Lemma simplify_instantiate_atom : forall (t : formula) s n, (exists a, t = atom a) -> instantiate s n t = t.
Proof. intros *. case => a. move => ->. reflexivity. Qed.
Lemma simplify_instantiate_U : forall (s t : formula) (n : nat), instantiate s n (U t) = U (instantiate s n t).
Proof. auto. Qed.
Lemma simplify_instantiate_S : forall (s t1 t2 t3 : formula) (n : nat), instantiate s n (S t1 t2 t3) = S (instantiate s n t1) (instantiate s n t2) (instantiate s n t3).
Proof. auto. Qed.
Lemma simplify_instantiate_P : forall (s t1 t2 t3 : formula) (n : nat), instantiate s n (P t1 t2 t3) = P (instantiate s n t1) (instantiate s n t2) (instantiate s n t3).
Proof. auto. Qed.
Lemma simplify_atom_get_label : forall t, (exists a, t = atom a) -> (atom (get_label t)) = t.
Proof. intros *. case => a. move => ->. reflexivity. Qed.
Lemma simplify_instantiate_one : forall s n, instantiate s n one = one.
Proof. intros; reflexivity. Qed.
Lemma simplify_instantiate_triangle : forall s n, instantiate s n triangle = triangle.
Proof. intros; reflexivity. Qed.

Hint Rewrite simplify_instantiate_U simplify_instantiate_S simplify_instantiate_P : simplify_formula.
Hint Rewrite simplify_instantiate_arrow : simplify_formula.
Hint Rewrite simplify_instantiate_var_eq simplify_instantiate_var_neq using omega : simplify_formula.
Hint Rewrite simplify_instantiate_quant using omega : simplify_formula.
Hint Rewrite @simplify_instantiate_atom using (eexists; reflexivity) : simplify_formula.
Hint Rewrite simplify_instantiate_one simplify_instantiate_triangle : simplify_formula.
Hint Rewrite @simplify_atom_get_label using (eexists; reflexivity) : simplify_formula.
Hint Rewrite Lc.instantiate_eq0 using done : simplify_formula.
