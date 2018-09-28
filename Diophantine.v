Load Common.

Require Import UserTactics.

Inductive diophantine : Set :=
  | dio_one (x : nat) : diophantine
  | dio_sum (x y z : nat) : diophantine
  | dio_prod (x y z : nat) : diophantine.

Module Diophantine.

Lemma eq_dec : forall (d1 d2 : diophantine), {d1 = d2} + {d1 <> d2}.
Proof.
case => [x |x y z |x y z]; case => [x' |x' y' z'|x' y' z'].
all : try (by right).
all : have := Nat.eq_dec x x'.
do ? (firstorder (do [by left | by right; case | auto])).
all : have := Nat.eq_dec y y'; have := Nat.eq_dec z z'.
all : do ? (firstorder (do [by left; f_equal | by right; case])).
Qed.

(*f encodes the variable valuation : V -> {1, 2, ...}*)
Definition eval (f : nat -> nat) (d : diophantine) : bool :=
  match d with
  | dio_one x => (1 + f x) =? 1
  | dio_sum x y z => (1 + f x) + (1 + f y) =? (1 + f z)
  | dio_prod x y z => (1 + f x) * (1 + f y) =? (1 + f z)
  end.

Inductive solvable (ds : list diophantine) : Prop :=
  | solution : (exists (f : nat -> nat), Forall (fun d => eval f d = true) ds) -> solvable ds.

End Diophantine.