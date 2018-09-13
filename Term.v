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

Require Export Label.
Require Import PeanoNat.
Require Import Omega.
Require Import UserTactics.

Inductive term : Set :=
  | free_var : label -> term
  | bound_var : nat -> term
  | term_app : term -> term -> term
  | term_abs : term -> term.

(*head form : x M1 .. Mn where x is free of bound*)
Inductive normal_form : term -> Prop :=
  | normal_head : forall (M : term), head_form M -> normal_form M
  | normal_abs : forall (M : term), normal_form M -> normal_form (term_abs M)
with head_form : term -> Prop :=
  | normal_free_var : forall (x : label), head_form (free_var x)
  | normal_bound_var : forall (n : nat), head_form (bound_var n)
  | normal_app : forall (M N : term), head_form M -> normal_form N -> head_form (term_app M N).

Inductive term_depth : nat -> term -> Prop :=
  | depth_free_var : forall (n : nat) (x : label), term_depth n (free_var x)
  | depth_bound_var : forall (n i : nat), term_depth n (bound_var i)
  | depth_term_app : forall (n : nat) (M N : term), term_depth n M -> term_depth n N -> term_depth (S n) (term_app M N) 
  | depth_term_abs : forall (n : nat) (M : term), term_depth n M -> term_depth (S n) (term_abs M).

Module Term.
(*instantiate x 0 M replaces the outermost bound variable in M by the free variable x*)
Fixpoint instantiate (x: label) (n : nat) (M : term) : term :=
  match M with
    | (free_var _) => M
    | (bound_var m) => if m =? n then free_var x else M
    | (term_app M N) => term_app (instantiate x n M) (instantiate x n N)
    | (term_abs M) => term_abs (instantiate x (S n) M)
  end.

(*bind x 0 M replaces occurrences of the free variable x in M by the outermost bound variable*)
Fixpoint bind (x : label) (level : nat) (M : term) : term :=
  match M with
  | (free_var y) => if Label.eqb x y then bound_var level else M
  | (bound_var _) => M
  | (term_app M N) => term_app (bind x level M) (bind x level N)
  | (term_abs M) => term_abs (bind x (S level) M)
  end.


Inductive fresh_in (x : label) : term -> Prop :=
  | fresh_in_free_var : forall (y : label), x <> y -> fresh_in x (free_var y)
  | fresh_in_bound_var : forall (n : nat), fresh_in x (bound_var n)
  | fresh_in_app : forall (M N : term), fresh_in x M -> fresh_in x N -> fresh_in x (term_app M N)
  | fresh_in_abs : forall (M : term), fresh_in x M -> fresh_in x (term_abs M).

(*locally closed up to n, lc 0 are well-formed terms*)
Inductive lc : nat -> term -> Prop :=
  | lc_free : forall (n: nat) (x: label), lc n (free_var x)
  | lc_bound : forall (m n: nat), n < m -> lc m (bound_var n) 
  | lc_app : forall (n: nat) (M N: term), lc n M -> lc n N -> lc n (term_app M N)
  | lc_abs : forall (n: nat) (M: term), lc (S n) M -> lc n (term_abs M).

Module Lc.

Lemma instantiate_iff : forall M x n, lc (1 + n) M <-> lc n (instantiate x n M).
Proof.
move => M x n; split.
{
elim : M x n; cbn.

auto using lc.

move => n x m; inversion.
have : n = m \/ n < m by omega.
case; intro; inspect_eqb; auto using lc.

all: intros; gimme lc; inversion; auto using lc.
}

{
elim : M x n; cbn.

auto using lc.

move => n x m.
have : n = m \/ n <> m by omega.
case; intro; inspect_eqb; inversion; constructor; omega.

all: intros; gimme lc; inversion; constructor; eauto.
}
Qed.


Lemma instantiate_bind : forall (x : label) (M : term) (n : nat), lc n M -> (instantiate x n (bind x n M)) = M.
Proof.
move => x.
elim; cbn.

move => y n.
have := Label.eq_dec x y.
case.

move => H; move /Label.eqb_eq : (H) => ->; cbn; subst; by inspect_eqb.
move => H; move /Label.neqb_neq : (H) => ->; by cbn.

move => i j; inversion.
by inspect_eqb.

all: intros; gimme lc; inversion; f_equal; eauto.
Qed.
End Lc.


Lemma instantiate_normal_form : forall (N : term) (x : label) (n : nat), 
  normal_form N -> normal_form (instantiate x n N).
Proof.
move => N x n.
suff : (normal_form N -> normal_form (instantiate x n N)) /\ 
  (head_form N -> head_form (instantiate x n N)); first intuition.
elim : N n.
intros until 0; cbn; auto.
move => n n'; cbn; case : (n =? n'); auto using normal_form, head_form.
(*case app*)
move => N IH1 M IH2 n; cbn.
split; inversion.
gimme head_form; inversion.
constructor; constructor; firstorder.
constructor; firstorder.
(*case abs*)
move => N IH n; cbn.
split; inversion.
gimme head_form; inversion.
apply normal_abs; firstorder.
Qed.


Lemma swap_instantiations : forall (x y : label) (M : term) (n m : nat), 
  n <> m -> instantiate x n (instantiate y m M) = instantiate y m (instantiate x n M).
Proof.
move => x y.
elim; cbn.
done.

move => i n m ?.
have : i = m \/ i <> m by omega.
have : i = n \/ i <> n by omega.

case; intro; case; intros; do ? inspect_eqb; cbn; by do ? inspect_eqb.

all: intros; f_equal; eauto.
Qed.


Lemma fresh_in_instantiate : forall (M : term) (x y : label) (n : nat), x <> y -> fresh_in x M -> fresh_in x (instantiate y n M).
Proof.
elim; cbn.

done.

move => i x y j.
case : (i =? j); eauto using fresh_in.

all: intros; gimme fresh_in; inversion; eauto using fresh_in.
Qed.


Lemma fresh_in_bind : forall (x : label) (M : term) (n : nat), fresh_in x (bind x n M).
Proof.
move => x.
elim; cbn.

move => y n.
have := Label.eq_dec x y.
case.

1: move /Label.eqb_eq => ->.
2: move => H; move /Label.neqb_neq : (H) => ->.

all: auto using fresh_in.
Qed.


Lemma normal_bind : forall (x : label) (N : term) (n : nat), 
  (normal_form N -> normal_form (bind x n N)) /\ (head_form N -> head_form (bind x n N)).
Proof.
intro; elim; cbn.

move => y; intros.
case : (Label.eqb x y); auto using normal_form, head_form.

auto using normal_form, head_form.

intros; split; inversion.
gimme head_form; inversion.
constructor.
1-2: constructor; firstorder.

intros; split; inversion.
gimme head_form; inversion.
apply : normal_abs; firstorder.
Qed.


Lemma relax_term_depth : forall (M : term) (n m : nat), term_depth n M -> n <= m -> term_depth m M.
Proof.
elim; auto using term_depth.

move => M IHM N IHN n m.
inversion => ?.
have : m = S (Nat.pred m) by omega.
move => ->.
apply : depth_term_app. 
apply : IHM; eassumption + omega.
apply : IHN; eassumption + omega.

move => M IH n m.
inversion => ?.
have : m = S (Nat.pred m) by omega.
move => ->.
apply : depth_term_abs. 
apply : IH; eassumption + omega.
Qed.


Lemma exists_term_depth : forall (M : term), exists (n : nat), term_depth n M.
Proof.
elim.
1-2: intros; exists 0; auto using term_depth.

move => M [n_M ?] N [n_N ?].
exists (S (n_M + n_N)).
apply : depth_term_app.
1-2: apply : relax_term_depth; eassumption + omega.

move => M [n_M ?].
eauto using term_depth.
Qed.


Lemma bind_depth : forall (n m : nat) (x : label) (M : term), term_depth n (bind x m M) -> term_depth n M.
Proof.
intros until 0.
elim : M n m; cbn.

1-2: intros; constructor.

all: intros; gimme term_depth; inversion; constructor; eauto.
Qed.


Lemma bind_instantiate : forall (x : label) (M : term) (n : nat), fresh_in x M -> (bind x n (instantiate x n M)) = M.
Proof.
move => x.
elim; cbn.

move => y n.
inversion.
gimme where (x <> y).
move /Label.neqb_neq => ->; done.

move => i j; inversion.
have : i = j \/ i <> j by omega.
case; intro; inspect_eqb; cbn => //.
subst.
have : x = x by done.
by move /Label.eqb_eq => ->.

all: intros; gimme fresh_in; inversion; f_equal; auto.
Qed.
End Term.

