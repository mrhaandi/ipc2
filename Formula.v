Load Common.

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


Lemma neq_neqb : forall (a b : label), a <> b -> (eqb a b = false).
Proof.
case => a1 a2; case => b1 b2; cbn.
have := Nat.eq_dec a1 b1; have := Nat.eq_dec a2 b2.
case => ?; case => ?; first (by subst); move => _.
all : match goal with [H : _ <> _ |- _] => move /Nat.eqb_neq : H => -> end.
all : auto using Bool.andb_false_r.
Qed.
End Label.


Inductive formula : Set :=
    | var : nat -> formula
    | atom : label -> formula
    | arr : formula -> formula -> formula
    | quant : formula -> formula.


Definition get_label (s : formula) : label :=
  match s with
  | atom a => a
  | _ => (0,0) (*to be replaced by some inhabitant of label or make function partial*)
  end.

Fixpoint substitute_label (a b : label) (t : formula) : formula :=
  match t with
    | (atom c) => if Label.eqb a c then (atom b) else t
    | (var _) => t
    | (arr s' t') => arr (substitute_label a b s') (substitute_label a b t')
    | (quant t') => quant (substitute_label a b t')
  end.

(*a is bindable in t if it does not appear free in t*)
Inductive fresh_in (a: label) : formula -> Prop :=
  | fresh_in_var : forall (n : nat), fresh_in a (var n)
  | fresh_in_atom : forall (b: label), a ≠ b -> fresh_in a (atom b)
  | fresh_in_arr : forall (s t: formula), fresh_in a s -> fresh_in a t -> fresh_in a (arr s t)
  | fresh_in_quant : forall (s: formula), fresh_in a s -> fresh_in a (quant s).


(*replace free occurrences of a in t by index n*)
Fixpoint bind (a: label) (n : nat) (t : formula) : formula :=
  match t with
    | (atom b) => if Label.eqb a b then var n else t
    | (var _) => t
    | (arr s t) => arr (bind a n s) (bind a n t)
    | (quant t) => quant (bind a (S n) t)
  end.

(*
(*replace all occurrences of atom a by s in t*)
Fixpoint substitute (a : label) (s t : formula) : formula :=
  match t with
    | (atom c) => if Label.eqb a c then s else t
    | (var _) => t
    | (arr s' t') => arr (substitute a s s') (substitute a s t')
    | (quant t') => quant (substitute a s t')
  end.
*)


(*instantiate s 0 t replaces the outermost bound variable in t by s, i.e. t[0/s]*)
Fixpoint instantiate (s: formula) (n : nat) (t : formula) : formula :=
  match t with
    | (atom _) => t
    | (var m) => if n =? m then s else t
    | (arr s' t') => arr (instantiate s n s') (instantiate s n t')
    | (quant t') => quant (instantiate s (S n) t')
  end.


Fixpoint instantiate_prenex (f : nat -> option formula) (t : formula) : formula :=
  match t with
    | (atom _) => t
    | (var m) => match f m with | Some s => s | None => t end
    | (arr s' t') => arr (instantiate_prenex f s') (instantiate_prenex f t')
    | (quant t') => quant (instantiate_prenex (fun n => match n with | 0 => None | S n' => f n' end) t')
  end.


(*locally closed up to n, lc 0 are well-formed formulae*)
Inductive lc : nat -> formula -> Prop :=
    | lc_var : forall (m n: nat), n < m -> lc m (var n) 
    | lc_atom : forall (n: nat) (a: label), lc n (atom a)
    | lc_arr : forall (n: nat) (s t: formula), lc n s -> lc n t -> lc n (arr s t)
    | lc_quant : forall (n: nat) (t: formula), lc (S n) t -> lc n (quant t).


(*repeated instantiation by locally closed formulae*)
Inductive contains : formula -> formula -> Prop :=
  | contains_rfl : forall (s: formula), contains s s
  | contains_trans : forall (s t u: formula), lc 0 s -> contains (instantiate s 0 u) t -> contains (quant u) t.


(*chain s a params morally means that s can be instanciated as p1 -> ... -> pn -> a*)
Inductive chain (s : formula) (a : label) : list formula -> Prop :=
  | chain_nil : contains s (atom a) -> chain s a List.nil
  | chain_cons : forall (t u: formula) (ts: list formula), contains s (arr t u) -> chain u a ts -> chain s a (t :: ts).


(*prepends n quantifiers to a given formula*)
Fixpoint quantify_formula n t : formula := 
  match n with
  | 0 => t
  | Datatypes.S n' => quant (quantify_formula n' t)
  end.
