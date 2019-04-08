Load Common.

Require Import FormulaFacts.
Require Import ListFacts.

Require Import UserTactics.
Require Import MiscFacts.

Inductive derivation (Γ: list formula) : formula → Prop :=
  | ax : ∀ (s: formula), In s Γ → derivation Γ s
  | elim_arr : ∀ (s t : formula), derivation Γ (Formula.arr s t) → derivation Γ s → derivation Γ t
  | intro_arr : ∀ (s t : formula), derivation (s :: Γ) t → derivation Γ (Formula.arr s t)
  | elim_quant : ∀ (s t : formula), derivation Γ s → contains s t → derivation Γ t
  | intro_quant : ∀ (s: formula), 
   (forall (a: label), derivation Γ (instantiate (atom a) 0 s)) → derivation Γ (Formula.quant s).

Inductive normal_derivation : nat → list formula → formula → Prop :=
(*(s :: Γ) in derive_arr not a problem, context permutation is admissible*)
  | derive_arr : ∀ (n : nat) (Γ: list formula) (s t: formula), 
    normal_derivation n (s :: Γ) t → normal_derivation (S n) Γ (Formula.arr s t)
  | derive_quant : ∀ (n : nat) (Γ: list formula) (s: formula), 
   (forall (a: label), normal_derivation n Γ (instantiate (atom a) 0 s) ) → normal_derivation (S n) Γ (Formula.quant s)
  | derive_atom : ∀ (n : nat) (Γ: list formula) (a: label) (s: formula) (params: list formula), 
      In s Γ → Formula.chain s a params → (Forall (normal_derivation n Γ) (params)) → normal_derivation (S n) Γ (Formula.atom a).

Axiom normal_derivation_completeness : forall (Γ: list formula) (s: formula), derivation Γ s → exists (n : nat), normal_derivation n Γ s.

(*tries to solve derivation Γ s automatically*)
Ltac derivation_rule := first
  [ apply ax => //; by list_element
  | ( do ? (apply intro_quant => //=; intro);
      do ? (apply intro_arr);
      apply ax => //; by list_element)
  (*| match goal with | [H : In ?s ?Γ |- derivation _ ?s] => apply ax; list_inclusion end (*slow, unnecessary*)*)
  | (by (eauto using derivation))].


Theorem normal_derivation_soundness : forall (n : nat) (Γ: list formula) (s: formula), normal_derivation n Γ s → derivation Γ s.
Proof.
elim; intros *.

(*base case n = 0*)
inversion.

move => IH Γ *.
gimme normal_derivation; inversion; try derivation_rule.

(*atom case*)
gimme In; move /ax.
gimme Forall;
gimme chain; elim.

(*zero step chain*) derivation_rule.
(*multistep chain*) move => ? ? t u *.
decompose_Forall. derivation_rule.
Qed.

(*inversion lemmas*)
Lemma inv_arr : forall (Γ : list formula) (s t : formula),
  derivation Γ (arr s t) -> derivation (s :: Γ) t.
Proof.
intros *.
move /normal_derivation_completeness => [? H].
inversion_clear H.
apply: normal_derivation_soundness; eassumption.
Qed.

Lemma inv_atom : forall (Γ : list formula) (a : label), derivation Γ (atom a) -> 
  exists (s : formula) (params : list formula), In s Γ /\ chain s a params /\ (Forall (derivation Γ) (params)).
Proof.
intros *.
move /normal_derivation_completeness => [? H].
inversion_clear H.
match goal with | [H : Forall _ _ |- _] => eapply Forall_impl in H; first last end.
intros.
eapply normal_derivation_soundness. eassumption.
exists s, params. auto.
Qed.

Lemma inv_normal_quant : forall (n : nat) (Γ: list formula) (s : formula), normal_derivation n Γ (quant s) ->
  exists (m : nat), n = S m /\ (forall (a: label), normal_derivation m Γ (instantiate (atom a) 0 s)).
Proof.
intros * => H.
inversion_clear H.
eexists; split; [reflexivity | assumption].
Qed.

Lemma inv_quant : forall (Γ: list formula) (s : formula), derivation Γ (quant s) ->
  (forall (a: label), derivation Γ (instantiate (atom a) 0 s)).
Proof.
intros *.
move /normal_derivation_completeness => [n HD].
move /inv_normal_quant : HD => [m [? ?]].
eauto using normal_derivation_soundness.
Qed.

Lemma inv_normal_arr : forall (n : nat) (Γ: list formula) (s t : formula), normal_derivation n Γ (arr s t) ->
  exists (m : nat), n = S m /\ normal_derivation m (s :: Γ) t.
Proof.
intros * => H.
inversion_clear H.
eexists; split; [reflexivity | assumption].
Qed.

(*decomposition tactics*)
Ltac decompose_normal_derivation := 
  do ? (
  lazymatch goal with
  | [H : Forall _ (_ :: _) |- _] => inversion_clear H
  | [H : Forall _ nil |- _] => inversion_clear H
  | [H : normal_derivation _ _ (quant _) |- _ ] => 
    let n := fresh "n" in move /inv_normal_quant : H => [n [? H]]
  | [H : normal_derivation _ _ (arr _ _) |- _ ] => 
    let n := fresh "n" in move /inv_normal_arr : H => [n [? H]]
  | [H : normal_derivation _ _ _ |- _] => move : H; inversion
  end).

Ltac decompose_chain :=
  do ? (
  match goal with
  | [H : chain ?s _ _ |- _] =>
    match eval hnf in s with
    | arr _ _ => (move /chain_arr : H => [? [? H]]); subst
    | atom _ => (move /chain_atom : H => [? ?]); try done; subst
    end
  end).

Ltac decompose_derivation := 
  do ? (
  match goal with
  | [H : derivation _ ?s |- _] => 
    match eval hnf in s with
    | arr _ _ => move /inv_arr : H => H
    | atom _ => 
      let s := fresh in 
      let H' := fresh in
      move /inv_atom : H => [s [? [H' [? ?]]]]
    end
  end).

Ltac decompose_contains :=
  match goal with
  | [H : contains _ _ |- _] => inversion_clear H
  end.


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

Tactic Notation "gimme" "where" constr(p) := 
  lazymatch goal with
  | [H : context[p] |- _] => move : H
  end.

Lemma substitute_normal_derivation : forall (n : nat) (s : formula) (Γ : list formula) (a b : label), 
  normal_derivation n Γ s -> normal_derivation n (map (substitute_label a b) Γ) (substitute_label a b s).
Proof.
elim /lt_wf_ind.

intros * => IH; intros.

gimme normal_derivation; inversion; cbn.
(*arr*)
apply : derive_arr.
rewrite <- map_cons.
apply : IH; try done + omega.
(*quant*)
match goal with [_ : context G [instantiate _ _ ?s'] |- _] => rename s' into s end.
apply : derive_quant => c.
case : (Label.eq_dec c a).

intro; subst c.
have [d Hd] := exists_fresh ([atom a; atom b; s] ++ (map (substitute_label a b) Γ)).
decompose_Forall.

do 2 (gimme shape (fresh_in d (atom _)); inversion).
rewrite -> (@instantiate_renaming_eq _ _ _ d); auto.
rewrite -> (@map_substitute_fresh_label d a (map (substitute_label a b) Γ)); auto.

intros.
rewrite -> instantiate_renaming_neq; auto.

(*atom*)
set Γ' := map (substitute_label a b) Γ.
match goal with [_ : In ?s' Γ |- _] => rename s' into s end.
set s' := (substitute_label a b) s.
rewrite if_fun.
match goal with [_ : chain s ?a' params |- _] => rename a' into c end.
set a' := (if Label.eqb a c then b else c).
set params' := map (substitute_label a b) params.
have ? : In s' Γ' by apply : in_map; assumption.
have ? : chain s' a' params' by apply : substitute_chain; assumption.

have ? : Forall (normal_derivation n0 Γ') params'.
gimme Forall; move : IH; clear; revert dependent params.
elim; cbn; first done.

intros; decompose_Forall.
eauto.

apply : derive_atom; try eassumption.
Qed.


Lemma substitute_derivation_bindable : forall (s : formula) (Γ : list formula) (a b : label), 
  Forall (fresh_in a) Γ -> derivation Γ s -> derivation Γ (substitute_label a b s).
Proof.
intros.
have : Γ = map (substitute_label a b) Γ by apply map_substitute_fresh_label.
move => ->.
gimme derivation; move /normal_derivation_completeness => [? ?].
eauto using normal_derivation_soundness, substitute_normal_derivation.
Qed.


(*the usual presentation of intro_quant*)
Theorem intro_quant_fresh : ∀ (s: formula) (Γ : list formula) (a : label), 
  Forall (fresh_in a) Γ -> fresh_in a s ->
  (derivation Γ (instantiate (atom a) 0 s)) → derivation Γ (Formula.quant s).
Proof.
move => s Γ a H *.
apply intro_quant => b.
gimme derivation.
move /(substitute_derivation_bindable b H).
rewrite -> rename_instantiation; auto.
Qed.


Lemma normal_weakening : ∀ (n : nat) (Γ Δ: list formula), 
  (∀ (s : formula), In s Γ → In s Δ) → forall (t: formula), normal_derivation n Γ t → normal_derivation n Δ t.
Proof.
elim.
intros * => ? ?; inversion.

move => n IH Γ Δ H_in t; inversion.
(*case arr*)
constructor. apply: IH; try eassumption.
move => s'. move : (H_in s').
list_inclusion.

(*case quant*)
constructor. eauto.
(*case atom*)
apply: derive_atom; eauto.
apply : Forall_impl; last eassumption.
eauto.
Qed.


Lemma weakening : ∀ (Γ Δ: list formula) (t: formula), 
  derivation Γ t → (∀ (s : formula), In s Γ → In s Δ) → derivation Δ t.
Proof.
intros *.
move /normal_derivation_completeness; case.
eauto using normal_derivation_soundness, normal_weakening.
Qed.


Lemma weakening_cons : ∀ (Γ: list formula) (s t: formula), derivation Γ t → derivation (s :: Γ) t.
Proof.
firstorder using weakening.
Qed.


Lemma context_generalization : forall (Γ Δ: list formula) (t : formula), 
  derivation Γ t -> (forall (s : formula), In s Γ -> derivation Δ s) -> derivation Δ t.
Proof.
elim.
(*base case*)
intros.
apply: (weakening (Γ := [])) => //.
(*inductive case*)
intros * => IH.
intros until 1 => H'.
have ? : derivation l (arr a t) by derivation_rule.
have ? : derivation Δ (arr a t) => //.
apply IH => //; intros; apply H'; list_inclusion.
have ? : derivation Δ a by apply H'; list_inclusion.
derivation_rule.
Qed.


Lemma context_generalization_app : forall (Γ Δ Γ': list formula) (t : formula), 
  derivation (Γ ++ Δ) t -> (forall (u : formula), In u Γ -> derivation Γ' u) -> derivation (Γ' ++ Δ) t.
Proof.
intros.
apply: (context_generalization). eassumption.
move => s H_In.
apply in_app_or in H_In.
case : H_In => H_In.
apply : (weakening (Γ := Γ')); auto with *.
derivation_rule.
Qed.


(*looks for In/chain statements and eliminates impossible cases*)
Ltac filter_context_chain := 
  let filter_context_chain_inner H_In :=
    move => H_In; subst => //;
    (do ? (
      match goal with 
      | [|- chain ?s _ _ -> _] => 
        match eval hnf in s with
        | (arr _ _) => (let H' := fresh in move /chain_arr => [? [? H']]; move: H'; subst => //)
        | (atom _) => (move /chain_atom => [? ?]; subst => //)
        end
      end))
  in
    match goal with | [ H_In : In ?s _, H_c : chain ?s _ _ |- _] => move: H_In H_c;
    rewrite ? (in_app_iff, in_cons_iff, or_assoc);
    let t := (filter_context_chain_inner H_In) in decompose_or t end.


(*looks for In statements to derive current goal and eliminates trivial cases*)
Ltac filter_context_derivation := 
  let rec filter_context_derivation_inner H_In :=
    move => H_In; subst; try derivation_rule
  in
  match goal with | [ H_In : In ?s _ |- derivation _ ?s] => 
    move: H_In;
    rewrite ? (in_app_iff, in_cons_iff, or_assoc);
    let t := filter_context_derivation_inner H_In in decompose_or t
  end.