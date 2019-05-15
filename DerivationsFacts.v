Require Import Utf8.
Require Import List.
Import ListNotations.
Require Import Omega.

From Coq Require Import ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Maximal Implicit Insertion.

Require Import FormulaFacts.
Require Import Derivations.
Require Import DerivationDepth.
Require Import F_adapter.
Require Import ListFacts.

Require Import UserTactics.
Require Import MiscFacts.
Require Import Psatz.


Theorem normal_derivation_completeness : forall (Gamma: list formula) (t: formula), 
  Forall well_formed_formula Gamma -> well_formed_formula t -> derivation Gamma t -> exists (n : nat), normal_derivation n Gamma t.
Proof.
move => *. grab derivation. move /derivation_to_iipc2. move /(_ ltac:(done) ltac:(done)).
by apply /iipc2_to_normal_derivation.
Qed.

Lemma derivation_iff_normal_derivation : forall (Gamma: list formula) (t: formula), 
  Forall well_formed_formula Gamma -> well_formed_formula t -> derivation Gamma t <-> exists (n : nat), normal_derivation n Gamma t.
Proof.
move => *.
constructor => [? | [? ?]].
by apply : normal_derivation_completeness.
apply : normal_derivation_soundness; by eassumption.
Qed.

Print Assumptions normal_derivation_completeness.


(*inversion lemmas*)
Lemma inv_arr : forall (Γ : list formula) (s t : formula),
  Forall well_formed_formula Γ -> well_formed_formula (arr s t) ->
  derivation Γ (arr s t) -> derivation (s :: Γ) t.
Proof.
move => *. grab derivation.
rewrite ? derivation_iff_normal_derivation //.
move => [?]. inversion. eexists. by eassumption.
all: grab well_formed_formula; inversion; by [| constructor].
Qed.

Lemma inv_atom : forall (Γ : list formula) (a : label), Forall well_formed_formula Γ -> derivation Γ (atom a) -> 
  exists (s : formula) (params : list formula), In s Γ /\ chain s a params /\ (Forall (derivation Γ) (params)).
Proof.
move => *. grab derivation.
rewrite derivation_iff_normal_derivation //.
move => [?]. inversion.
do 2 eexists.
split. by eassumption.
split. by eassumption.
grab chain. move /chain_param_wff.
apply : unnest. grab (Forall well_formed_formula). move /Forall_In_iff. by auto.
revert dependent params. elim => //.
move => *. decompose_Forall. constructor. 
apply derivation_iff_normal_derivation => //. eexists. by eassumption.
by eauto.
by constructor.
Qed.


Lemma inv_quant : forall (Γ: list formula) (s : formula), 
  Forall well_formed_formula Γ -> well_formed_formula (quant s) -> derivation Γ (quant s) ->
  (forall (a: label), derivation Γ (instantiate (atom a) 0 s)).
Proof.
move => *. grab derivation. rewrite ? derivation_iff_normal_derivation //.
move => [?]. inversion. eexists. by eauto.
grab well_formed_formula. inversion.
apply : Lc.instantiate_pred; by [ | constructor].
Qed.

Ltac decompose_derivation := 
  match goal with
  | [H : derivation _ ?s |- _] => 
    match eval hnf in s with
    | arr _ _ => (move /inv_arr : H; apply : unnest; [| apply : unnest]); first last; first move => H
    (*| atom _ => 
      let s := fresh in 
      let H' := fresh in
      move /inv_atom : H => [s [? [H' [? ?]]]]*)
    end
  end.
