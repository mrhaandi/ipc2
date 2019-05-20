(*common header begin*)
Require Import Utf8.
From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Maximal Implicit Insertion.
(*common header end*)

Require Import Arith.
Require Import PeanoNat.
Require Import Psatz. (*lia : linear integer arithmetic, nia : non-linear integer arithmetic*)


Lemma lebP m n : reflect (m <= n) (m <=? n).
Proof.
apply: (iffP idP); by move /Nat.leb_le.
Qed.

Lemma eqbP m n : reflect (m = n) (m =? n).
Proof.
apply: (iffP idP); by move /Nat.eqb_eq.
Qed.

Ltac inspect_eqb_aux t := try (
  match goal with
  | [ |- context [?x =? ?y]] => 
    do [have -> : (x =? y) = false by apply /eqbP; t | have -> : (x =? y) = true by apply /eqbP; t]
  | [ |- context [?x <=? ?y]] => 
    do [have -> : (x <=? y) = false by apply /lebP; t |  have -> : (x <=? y) = true by apply /lebP; t]
  end).

Tactic Notation "inspect_eqb" := inspect_eqb_aux lia.


From LCAC Require Import ssrnat_ext.
From mathcomp Require Import eqtype ssrnat.

Ltac unfoldN := do ? arith_hypo_ssrnat2coqnat; do ?unfold addn, subn, muln, addn_rec, subn_rec, muln_rec, leq, Equality.sort, nat_eqType in *.

Ltac decompose_or tactic :=
  match goal with
  | [ |- _ \/ _ -> _] => case; [tactic | decompose_or tactic]
  | _ => tactic
  end.

(*does not touch existing evars*)
Tactic Notation "grab" "shape" open_constr(p) := 
lazymatch goal with
| [H : p |- _] => let t := type of H in 
  tryif has_evar t then fail else unify p t; move : H
end.

(*idtac if p is the prefix of q otherwise fail*)
Ltac is_prefix p q :=
  lazymatch q with
  | p => idtac
  | (?r _) => is_prefix p r
  end.

(*idtac if q => (_ -> ... -> (p _ .. _)) otherwise fail*)
Ltac results_in p q :=
  lazymatch q with
  | p => idtac
  | (_ -> ?r) => results_in p r
  | (?r _) => results_in p r
  end.

(*reverts hypothesis starting with p and containing q*)
Tactic Notation "grab" constr(p) := 
  match goal with [H : ?t |- _] => 
    tryif (results_in p t) then move : H else fail
  end.

(*reverts assumption containing p*)
Tactic Notation "grab" "where" constr(p) :=
  match goal with [H : context[p] |- _] => move : H end.

(*reverts hypothesis starting with p and containing q*)
Tactic Notation "grab" constr(p) "where" constr(q) := 
  match goal with [H : context[q] |- _] => 
    let t := type of H in tryif (is_prefix p t) then move : H else fail
  end.

Tactic Notation "inversion" := let H := fresh "top" in 
  do ? (match goal with [E : ?t = ?u |- _] => do [is_var t | is_var u]; change (unkeyed (t = u)) in E end); (*hide equalities*)
  intro H; inversion H; clear H; (*invert top*)
  subst; (*do ? (match goal with [E : ?t = ?u |- _] => is_var u; tryif is_var t then subst t else subst u end); (*propagate substitutions*)*)
  do ? (match goal with [E : unkeyed ?e |- _] => change e in E end). (*restore equalities*)

(*
Ltac inspect_eqb := try (
  match goal with
  | [ |- context [?x =? ?y]] => 
    do [(have : x <> y by do [lia | nia]); move /Nat.eqb_neq => -> |
     (have : x = y by do [lia | nia]); move /Nat.eqb_eq => ->]
  end).
*)

(*bug: have behaves differently than suff*)
(*decomposes top, a->b besomes b with seperate goal a*)
(*decomposes top, forall a, b besomes b containing evar ?x*)
Ltac nip := match goal with 
  | [ |- (?A -> ?B) -> _ ] => 
    let H := fresh "H" in suff : A; first (move => H; move /(_ H); clear H); first last 
  | [ |- (forall (A : ?T), _) -> _ ] => 
    let x := fresh "x" in evar(x : T); let x' := eval red in x in move /(_ x')
  | _ => idtac
  end.


(*transforms a goal (A -> B) -> C into goals A and B -> C*)
Lemma unnest : forall (A B C : Prop), A -> (B -> C) -> (A -> B) -> C.
Proof.
auto.
Qed.

(*duplicates first argument*)
Lemma duplicate : forall (A : Prop), A <-> A /\ A.
Proof.
move => ?. constructor; by [ | case].
Qed.

(*swaps first two arguments*)
Lemma swap (P Q R : Prop) : (P -> Q -> R) -> (Q -> P -> R).
Proof. by auto. Qed.


Ltac do_first_tac n t :=
  match n with
  | 0%nat => idtac
  | 1%nat => t
  | (Datatypes.S ?n') => t; first (do_first_tac n' t)
  end.

Ltac do_last_tac n t :=
  match n with
  | 0%nat => idtac
  | 1%nat => t
  | (Datatypes.S ?n') => t; last (do_last_tac n' t)
  end.

(*applies n times tactic t recursively in the first/last generated goal*)
Tactic Notation "do_first" constr(n) tactic(t) := do_first_tac n t.
Tactic Notation "do_last" constr(n) tactic(t) := do_last_tac n t.


(*tries to simplify nat comparisons*)
Ltac inspect_eqn :=
  match goal with
  | [ |- context [?x == ?y]] => 
    do [(have : (x == y) = false by apply /eqP; unfoldN; lia); move => -> |
     (have : (x == y) = true by apply /eqP; unfoldN; lia); move => ->]
  | [ |- context [?x <= ?y]] => 
    do [(have : (x <= y) = false by apply /eqP; unfoldN; lia); move => -> |
     (have : (x <= y) = true by apply /eqP; unfoldN; lia); move => ->]
  end.