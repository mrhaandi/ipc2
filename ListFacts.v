(*common header begin*)
Require Import Utf8.
From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Maximal Implicit Insertion.
(*common header end*)

Require Import List.
Import ListNotations.

Require Import Omega.
Require Import UserTactics.


Lemma in_cons_iff : forall {A : Type} {a b : A} {l : list A}, In b (a :: l) <-> (a = b \/ In b l).
Proof.
auto with *.
Qed.


Lemma Forall_tl (T : Type) (P : T -> Prop) : forall (ss : list T), Forall P ss -> Forall P (tl ss).
Proof.
case => //.
intros; gimme Forall; inversion; assumption.
Qed.


Lemma Forall_app (T : Type) (P : T -> Prop) : forall (A B : list T), Forall P (A ++ B) <-> Forall P A /\ Forall P B.
Proof.
elim; first by firstorder done.
intros until 0 => IH.
intros.
constructor.
inversion.
firstorder (by constructor).
move => [HP1 HP2].
inversion_clear HP1.
rewrite <- app_comm_cons.
firstorder (by constructor).
Qed.


Lemma Forall_cons : forall (T : Type) (P : T -> Prop) (A : list T) (a : T),
  Forall P (a :: A) -> P a /\ Forall P A.
Proof.
intros; gimme Forall; inversion; auto.
Qed.


Lemma Forall_In : forall (T : Type) (P : T -> Prop) (A : list T) (a : T), In a A -> Forall P A -> P a.
Proof.
move => T P.
elim => [a | b A IH a]; first case.
move /in_cons_iff.
case => [-> | ?]; move /Forall_cons => [? ?]; auto.
Qed.


Lemma Forall_flat_map (T U: Type) (P : T -> Prop) : forall (ds : list U)
    (params : list T) 
    (f : U -> list T)
     (d : U), Forall P (flat_map f ds) ->
In d ds -> Forall P (f d).
Proof.
elim; first done.
intros until 0 => IH.
cbn.
intros until 0 => H.
intros until 0.
move /Forall_app => [? ?].
case; [by intros; subst | auto].
Qed.


(*destructs all assumptions of the shape Forall P l where l matches cons, nil or app*)
Ltac decompose_Forall := 
  do ? (
  match goal with
  | [H : Forall _ (_ :: _) |- _] => inversion_clear H
  | [H : Forall _ nil |- _] => inversion_clear H
  | [H : Forall _ (_ ++ _) |- _] => move /Forall_app : H => [? ?]
  end).


(*tactic to decide list membership*)
Ltac list_element :=
  (try assumption);
  lazymatch goal with
  | [|- In _ (_ :: _)] => first [by left | right; list_element]
  | [|- In _ (_ ++ _)] => apply in_or_app; first [left; list_element | right; list_element]
  | [|- In ?a ?l] => let l' := eval hnf in l in progress(change (In a l')); list_element
  end.


(*tactic to decide list inclusion*)
Ltac list_inclusion := 
  intros; do ? (match goal with | [H : In ?a _ |- context [?a]] => move: H end);
  match goal with
  | [ |- In _ _] => list_element
  | _ => rewrite ? (in_app_iff, in_cons_iff); intuition (subst; tauto)
  end.


Ltac list_inclusion_veryfast := 
  let rec list_inclusion_rec :=
    lazymatch goal with
    | [ |- In _ _] => list_element
    | [ |- In ?b (?a :: _) -> _] => 
      case /(in_inv (a := a) (b := b)) => [?|]; [subst; list_inclusion_rec | list_inclusion_rec]
    | [ |- In ?b (_ ++ _) -> _] => 
      case /(in_app_or _ _ b); list_inclusion_rec
    | [ |- In _ _ -> _] => move => ?; list_inclusion_rec
    end
  in
  intros;
  try (match goal with | [H : In ?a _ |- In ?a _] => move: H end); clear;
  list_inclusion_rec.


Lemma in_sub : forall (T : Type) (A B : list T) (a : T), In a A -> (forall (b : T), In b A -> In b B) -> In a B.
Proof.
auto.
Qed.

Lemma Forall_exists_monotone : forall (A : Type) (P : nat -> A -> Prop) (l : list A), 
  (forall (n m : nat) (a : A), P n a -> n <= m -> P m a) -> Forall (fun (a : A) => exists (n : nat), P n a) l ->
  exists (n : nat), Forall (P n) l.
Proof.
move => A P l H. elim : l.

intros; exists 0; auto.

move => a l IH; inversion.
gimme Forall. move /IH.
gimme where P; move => [n1 ?].
move => [n2 ?].
exists (n1+n2); constructor.
apply : H; [eassumption | omega].
apply : Forall_impl; last eassumption.
intros; apply : H; [eassumption | omega].
Qed.
