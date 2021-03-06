Load Common.

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
  derivation (ΓI ds ++ [U one; P one one one]) triangle.
Proof.
move => ds.
constructor.
apply : completeness.

have : [U one; P one one one] = [U one] ++ [] ++ [P one one one] by done.
move => ->.
move /normal_derivation_completeness => [? HD].

apply : soundness; try eassumption. 
all: move => s; case => //; move => <-.
exists 1; auto.
exists one, one, one; split; first auto.
exists 1, 1, 1. auto using interpretation_one.
Qed.

Print Assumptions correctness.
