Load Common.

Require Import PeanoNat.
Require Import ListFacts.
Require Import UserTactics.


(*HintDb containing lemmas regarding the last element of seq*)
Create HintDb seq.

Lemma seq_last : forall (start length : nat), 
  seq start (S length) = (seq start length) ++ [start + length].
Proof.
move => start length.
elim : length start.
intros; cbn; f_equal; omega.

move => length IH start; cbn.
f_equal.
have : start + S length = (S start) + length by omega.
move => ->.
apply : IH.
Qed.

Lemma repeat_last : forall (T : Type) (a : T) (length : nat), 
  repeat a (S length) = (repeat a length) ++ [a].
Proof.
move => T a length.
elim : length => //.

move => length IH; cbn.
f_equal.
auto.
Qed.


Lemma map_singleton (T U : Type) : forall (f : T -> U) (a : T), map f [a] = [f a].
Proof. reflexivity. Qed.

Lemma Forall_app_singleton : forall (T : Type) (P : T -> Prop) (l : list T) (a : T), 
  Forall P (l ++ [a]) <-> Forall P l /\ (P a).
Proof.
intros until 0.
split.
move /Forall_app.
intuition.
gimme Forall; by inversion.

rewrite ? Forall_forall.
intuition.
gimme In; rewrite ? in_app_iff.
intuition.
gimme In; inversion; done.
Qed.

Hint Rewrite seq_last : seq.
Hint Rewrite @repeat_last : seq.
Hint Rewrite map_app : seq.
Hint Rewrite @map_singleton : seq.
Hint Rewrite plus_O_n plus_n_O : seq.
Hint Rewrite @Forall_app_singleton : seq.
Hint Rewrite <- plus_n_O : seq.

(*list of pars of list elements along with their index starting with start*)
Fixpoint indexed (T : Type) (start : nat) (l : list T) :=
  match l with
  | nil => nil
  | (cons a l) => cons (start, a) (indexed (S start) l)
  end.


Lemma indexed_app : forall (v w : list nat) (n : nat), indexed n (v ++ w) = (indexed n v) ++ (indexed (length v+n) w).
Proof.
elim; cbn; first done.
move => a v IH w n.
have : S (length v + n) = length v + (S n) by omega.
move => ->.
f_equal; eauto.
Qed.

Hint Rewrite @indexed_app : seq.

Lemma in_indexed_in : forall (T : Type) (l : list T) (i n : nat) (a : T), In (i, a) (indexed n l) -> In a l.
Proof.
move => T.
elim; cbn; first done.
move => b l IH i n a.
case; first case; eauto.
Qed.

Lemma in_indexed_bounds : forall (T : Type) (l : list T) (i n : nat) (a : T), In (i, a) (indexed n l) -> n <= i /\ i < n + length l.
Proof.
move => T.
elim; cbn; first done.
move => b l IH i n a.
case; first case.
intros; omega.
move /IH.
case; intros; omega.
Qed.

Lemma in_indexed_eq : forall (T : Type) (l : list T) (i n : nat) (a b : T), In (i, a) (indexed n l) -> In (i, b) (indexed n l) -> a = b.
Proof.
move => T.
elim; cbn; first done.
move => c l IH i n a b.
case.
case=> ? ?.
case.
case=> ? ?; congruence.
subst.
move /in_indexed_bounds; intros; omega.
move => ?.
case.
case => ? ?; subst.
gimme In.
move /in_indexed_bounds; intros; omega.
eauto.
Qed.

Lemma in_in_indexed : forall (T : Type)  (a : T) (l : list T) (n : nat), In a l -> exists (i : nat), In (i, a) (indexed n l).
Proof.
move => T a.
elim => //.
move => b l IH n; cbn.
case.
intro; subst; exists n; by left.
move /IH; move /(_ (S n)). firstorder.
Qed.