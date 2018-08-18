From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Psatz. (*lia : linear integer arithmetic, nia : non-linear integer arithmetic*)
Require Import List.
Import ListNotations.

Require Import Arith.
Require Import Omega.
Ltac decompose_or tactic :=
  match goal with
  | [ |- _ \/ _ -> _] => case; [tactic | decompose_or tactic]
  | _ => tactic
  end.

(*destructs all assumptions of the shape Forall P l where l matches cons, nil or app*)
Ltac decompose_Forall := 
  do ? (
  match goal with
  | [H : Forall _ (_ :: _) |- _] => inversion_clear H
  | [H : Forall _ nil |- _] => inversion_clear H
  | [H : Forall _ (_ ++ _) |- _] => move /Forall_app : H => [? ?]
  end).

(*does not touch existing evars*)
Tactic Notation "gimme" "shape" open_constr(p) := 
lazymatch goal with
| [H : p |- _] => let t := type of H in 
  tryif has_evar t then fail else unify p t; move : H
end.

(*
(*uses documented uconstr but weird trickery*)
Ltac gimme_tac shape :=
let e := fresh in
refine (let e := shape in _);
let v := eval red in e in clear e;
match goal with H : ?C |- _ =>
unify v C; move : H
end.

Tactic Notation "gimme" uconstr(shape) := gimme_tac shape.
*)

(*reverts assumption with head p*)
Tactic Notation "gimme" constr(p) :=
  lazymatch goal with 
  | [ H : p _ _ _ _ _ _ _  |- _] => move : H
  | [ H : p _ _ _ _ _ _  |- _] => move : H
  | [ H : p _ _ _ _ _  |- _] => move : H
  | [ H : p _ _ _ _  |- _] => move : H
  | [ H : p _ _ _  |- _] => move : H
  | [ H : p _ _  |- _] => move : H
  | [ H : p _  |- _] => move : H
  | [ H : p  |- _] => move : H
  end.

Tactic Notation "inversion" := let H := fresh "top" in 
  do ? (match goal with [E : ?t = ?u |- _] => is_var u; change (unkeyed (t = u)) in E end); (*hide equalities*)
  intro H; inversion H; clear H; (*invert top*)
  subst; (*do ? (match goal with [E : ?t = ?u |- _] => is_var u; tryif is_var t then subst t else subst u end); (*propagate substitutions*)*)
  do ? (match goal with [E : unkeyed ?e |- _] => change e in E end). (*restore equalities*)

(*tends to overlook equalities
Tactic Notation "inversion" := let H := fresh "top" in intro top; inversion_clear top.
*)


Ltac inspect_eqb := try (
  match goal with
  | [ |- context [?x =? ?y]] => 
    do [(have : x <> y by do [lia | nia]); move /Nat.eqb_neq => -> |
     (have : x = y by do [lia | nia]); move /Nat.eqb_eq => ->]
  end).

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


Ltac do_first_tac n t :=
  match n with
  | 0%nat => idtac
  | (Datatypes.S ?n') => t; first (do_first_tac n' t)
  end.

(*applies n times tactic t recursively in the first generated goal*)
Tactic Notation "do_first" constr(n) tactic(t) := do_first_tac n t.