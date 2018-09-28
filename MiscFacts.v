Load Common.

Require Import PeanoNat.
Require Import Psatz.

Require Import UserTactics.

(*
Lemma if_eq : forall (f : nat -> nat) (x y : nat), (if y =? x then f x else f y) = f y.
Proof.
move => f x y.
have := Nat.eq_dec x y.
case; intros; inspect_eqb; auto.
Qed.


Lemma if_elim {T : Type} (P : T -> Prop) (m n : nat) (a b : nat -> nat -> T) : 
  P (a m n) -> P (b m n) -> P (if m =? n then a m n else b m n).
Proof.
intros.
case : (Nat.eq_dec m n); intros;
inspect_eqb; assumption.
Qed.
*)

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