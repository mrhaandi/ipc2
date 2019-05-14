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

Print Assumptions normal_derivation_completeness.