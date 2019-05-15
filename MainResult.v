Require Import Utf8.
Require Import List.
Import ListNotations.
Require Import Omega.

From Coq Require Import ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Maximal Implicit Insertion.

Require Import Soundness.
Require Import Completeness.

(*
given set "ds" of constraints (representing a diophantine equation),
we have that "ds" is solvable (there is a satisfying valuation)
iff
"triangle" is derivable in the environment ΓI ds ++ [U one; P one one one]
in the intuitionistic second-order propositional logic (IPC2)

the reduction assumes normalization (cf. Derivations.v) of system F (corresponds to IPC2 by the Curry-Howard-isomorphism)
and the Hilbert's epsilon combinator (cf. Coq.Logic.Epsilon)
*)
Theorem correctness : forall (ds : list diophantine), Diophantine.solvable ds <->
  IIPC2.iipc2 (ΓI ds ++ [U one; P one one one]) triangle.
Proof.
move => ds.
constructor.
move /completeness. move /F_adapter.derivation_to_iipc2. apply; inspect_wff.


have -> : [U one; P one one one] = [U one] ++ [] ++ [P one one one] by done.
move /F_adapter.iipc2_to_normal_derivation => [?].

apply /soundness.
all: move => s; case => //; move => <-.
exists 1; auto.
exists one, one, one; split; first auto.
exists 1, 1, 1. auto using interpretation_one.
Qed.


Print Assumptions correctness.
