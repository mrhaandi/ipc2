Require Import Utf8.
Require Import List.
Import ListNotations.
Require Import Omega.

From Coq Require Import ssreflect ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Maximal Implicit Insertion.

Require Import PeanoNat.
Require Import Psatz.

Require Import UserTactics.



Lemma if_fun {T U : Type}: forall A (f : T -> U) a b, (if A then f a else f b) = f (if A then a else b).
Proof.
case => //.
Qed.

Lemma fold_sum_gt : forall l n m, n > m -> fold_left Nat.add l n > m.
Proof.
elim; cbn; first auto.
move => n l IH k m H; cbn.
apply : IH. lia.
Qed.

Lemma split_domain : forall (x : nat) (P Q : nat -> Prop),
  (forall (n : nat), (x = n \/ P n) -> Q n) <-> (Q x /\ (forall (n : nat), P n -> Q n)).
Proof.
firstorder (subst; done).
Qed.