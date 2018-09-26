(*common header begin*)
Require Import Utf8.
From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Maximal Implicit Insertion.

Require Import List.
Import ListNotations.
(*common header end*)

Require Import Omega.
Require Import Bool.

(*used for free variables*)
Definition label : Set := nat * nat.


Module Label.
Lemma eq_dec : forall (a b : label), {a = b} + {a <> b}.
Proof.
case => a1 a2; case => b1 b2.
have := Nat.eq_dec a1 b1; have := Nat.eq_dec a2 b2.
case => ?; case => ?; first auto.
all : right; case; auto.
Qed.


Definition eqb (a : label) (b : label) : bool :=
  match a, b with
  | (a1, a2), (b1, b2) => (a1 =? b1) && (a2 =? b2)
  end.


Lemma eqb_eq : forall (a b : label), (eqb a b = true) <-> a = b.
Proof.
move => a b.
constructor.
rewrite -> (surjective_pairing a), (surjective_pairing b); cbn.
case /andb_true_iff.
by move /Nat.eqb_eq => -> /Nat.eqb_eq => ->.

move => ->.
rewrite -> (surjective_pairing b); cbn.
by rewrite <- ? beq_nat_refl.
Qed.

Lemma eq_eqb : forall (a b : label), a = b -> (eqb a b = true).
Proof.
move => [a1 a2] [b1 b2]. case. move => -> ->. cbn.
by rewrite <- ? beq_nat_refl.
Qed.

Lemma neqb_neq : forall (a b : label), (eqb a b = false) <-> a <> b.
Proof.
case => a1 a2; case => b1 b2; cbn.
rewrite andb_false_iff; rewrite ? Nat.eqb_neq. split.

case; intro; case; intros; by subst.

have := Nat.eq_dec a1 b1; have := Nat.eq_dec a2 b2.
firstorder auto.
Qed.

Lemma neq_neqb: forall (a b : label), a <> b -> (eqb a b = false).
Proof.
move => [a1 a2] [b1 b2]. cbn.
rewrite andb_false_iff; rewrite ? Nat.eqb_neq.

have := Nat.eq_dec a1 b1; have := Nat.eq_dec a2 b2.
firstorder auto.
Qed.

End Label.