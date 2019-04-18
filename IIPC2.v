Require Import Formula.
Require Import FormulaFacts.
Require Import List.
Require Import ListFacts.
Require Import Psatz.
Require Import UserTactics.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(*s is well formed, if it contains no unbound De Bruijn indices*)
Definition well_formed_formula (s : formula) : Prop := lc 0 s.

(*second-order implicational intuitionistic propositional calculus IIPC2*)
Inductive iipc2 (Gamma: list formula) : formula -> Prop :=
  | iipc2_ax : forall (t: formula), Forall well_formed_formula Gamma -> In t Gamma -> iipc2 Gamma t
  | iipc2_elim_arr : forall (s t : formula), iipc2 Gamma (Formula.arr s t) -> iipc2 Gamma s -> iipc2 Gamma t
  | iipc2_intro_arr : forall (s t : formula), iipc2 (s :: Gamma) t -> iipc2 Gamma (Formula.arr s t)
  | iipc2_elim_quant : forall (s t : formula), well_formed_formula t -> iipc2 Gamma (Formula.quant s) -> iipc2 Gamma (instantiate t 0 s)
  | iipc2_intro_quant : forall (t: formula) (a : label), Forall (fresh_in a) Gamma -> iipc2 Gamma t -> iipc2 Gamma (Formula.quant (bind a 0 t)).


Lemma iipc2_wff : forall Gamma t, iipc2 Gamma t -> Forall well_formed_formula Gamma /\ well_formed_formula t.
Proof.
move => Gamma t. elim.
intros. split => //. apply : Forall_In; eassumption.

intros * => _ [?]. inversion. done.

intros * => _. case. inversion. intros. split; [eauto | by constructor].

intros * => ? _. case => ?. inversion. split => //. by apply : Lc.instantiate_pred.

intros * => _ _. case => ? ?. split => //. constructor. by apply : Lc.bind_succ.
Qed.