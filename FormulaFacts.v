Require Import Utf8.
Require Import List.
Import ListNotations.
Require Import Omega.

From Coq Require Import ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Maximal Implicit Insertion.

Require Import Psatz.
Require Import UserTactics.
Require Export Formula.
Require Import MiscFacts.
Require Import ListFacts.

(*Notation label := (nat * nat).*)

Module Lc.
Lemma instantiate_eq : forall (s t : formula) (m n : nat), lc m t -> m <= n -> instantiate s n t = t.
Proof.
intros s t.
induction t; intros m' n' Lc_t Le_mn; simpl; inversion Lc_t; eauto using f_equal, f_equal2, le_n_S.
by inspect_eqb.
Qed.

(*instantiating a locally closed formula t does nothing*)
Lemma instantiate_eq0 : forall (s t : formula) (n : nat), lc 0 t -> instantiate s n t = t.
Proof.
eauto using instantiate_eq with arith.
Qed.

Lemma relax : forall (s : formula) (n m : nat), lc n s -> n <= m -> lc m s.
Proof.
elim; intros.
grab lc; inversion; constructor; omega.
constructor.
grab lc; inversion; constructor; eauto.
grab lc; inversion; constructor; eapply H. eassumption. omega.
Qed.

Lemma instantiate_pred : forall s t n, lc (1 + n) s -> lc 0 t -> lc n (instantiate t n s).
Proof.
elim.
(*case var*)
move => n t m; intros.
simpl.
grab shape (lc (1 + m) _) => H_lc; inversion H_lc.
subst.
have : n = m \/ n < m by omega.
case; intros; inspect_eqb.
apply : Lc.relax; [eassumption | omega].
by constructor.
(*case atom*)
intros; constructor.
(*case arr*)
intros. simpl.
grab shape (lc _ (arr _ _)). inversion.
constructor; auto.
(*case quant*)
intros. simpl.
grab shape (lc _ (quant _)); inversion.
constructor. auto.
Qed.

Lemma succ_instantiate : forall s t n, lc n (instantiate t n s) -> lc 0 t -> lc (1 + n) s.
Proof.
elim => /=.
(*case var*)
move => n t m; intros.
have : (m = n) \/ (m <> n) by lia.
case => ?.
subst. by constructor.
grab (lc m). inspect_eqb. inversion. constructor. by lia.
(*case atom*)
intros; constructor.
(*case arr*)
intros. simpl.
grab shape (lc _ (arr _ _)). inversion.
constructor; eauto.
(*case quant*)
intros. simpl.
grab shape (lc _ (quant _)); inversion.
constructor. eauto.
Qed.

Lemma instantiate_prenex_eq : forall (t : formula) (n : nat) (f : nat -> option formula), 
  lc n t -> (forall (m : nat), m < n -> f m = None) -> instantiate_prenex f t = t.
Proof.
elim; intros * => IH; intros; simpl; grab lc; inversion.
(have : f n = None by auto) => ->.
auto.
done.
f_equal; eauto.
(*case quant*)
f_equal.
apply: IH. eassumption.
intros.
revert dependent m.
case; eauto with arith.
Qed.

Lemma bind_succ : forall a t n, lc n t -> lc (1+n) (bind a n t).
Proof.
move => a. elim; cbn.
all: intros; grab lc; inversion; f_equal; try (constructor; auto).
match goal with [|-context[if ?H then _ else _]] => case : H end.
all: by constructor.
Qed.
End Lc.


Lemma chain_arr : forall (s t : formula) (params : list formula) (a : label), chain (arr s t) a params -> 
  exists (ss : list formula), params = s :: ss /\ chain t a ss.
Proof.
move => s t params a.
case; intros; grab contains; inversion; eauto.
Qed.


Lemma chain_atom : forall (a b : label) (params : list formula), chain (atom a) b params -> params = [ ] /\ a = b.
Proof.
intros *.
inversion; grab contains; inversion; auto.
Qed.


Lemma instantiate_quantification (s t : formula) : forall (n : nat) (m : nat), 
  instantiate s m (quantify_formula n t) = quantify_formula n (instantiate s (n+m) t).
Proof.
elim; first auto.

intros.
have : forall n m, 1 + (n + m) = n + (1 + m) by intros; omega.
cbn => ->.
by f_equal.
Qed.


Lemma quantified_arrow_not_contains_atom : forall n s t a, contains (quantify_formula n (arr s t)) (atom a) -> False.
Proof.
elim; simpl; intros; grab contains; inversion.
grab contains; rewrite instantiate_quantification; eauto.
Qed.


Lemma instantiate_prenex_after_instantiate : forall (s t : formula) (n : nat) (f g : nat -> option formula), 
  lc 0 t 
  -> (forall (n' : nat), g n' = (fun m => if m =? n then Some t else f m) n')
  -> instantiate_prenex f (instantiate t n s) = instantiate_prenex g s.
Proof.
elim.
move => m ? n.
intros until 1 => Hg *.
case (Nat.eq_dec n m); intros; subst; cbn; rewrite Hg; do 2 inspect_eqb.
apply : Lc.instantiate_prenex_eq; [ eassumption | intros; omega ].
done.

(*case atom*) done.
(*case arr*) intros; cbn; f_equal; eauto.
(*case quant*)
intros * => IH.
intros until 1 => Hg *; cbn; f_equal.
apply : IH => //.
case.
by inspect_eqb.
move => n'.
rewrite Hg.
case (Nat.eq_dec n' n); intros; do 2 inspect_eqb => //.
Qed.


Lemma contains_to_prenex_instantiation : forall n s t s' t', 
  contains (quantify_formula n (arr s t)) (arr s' t') -> lc n t ->
  exists (f : nat -> option formula), t' = instantiate_prenex f t
  /\ (forall m, (m < n -> exists (u : formula), f m = Some u /\ lc 0 u)) 
  /\ (forall m, n <= m -> f m = None).
Proof.
elim.
(*base case n = 0*)
intros *.
inversion. intros.
exists (fun _ => None).
split.
apply eq_sym.
eapply Lc.instantiate_prenex_eq; last done. eassumption. split; [intros; omega | auto].
(*inductive case n > 0*)
simpl.
intros * => IH; intros.
grab contains; inversion.
match goal with | [_ : lc 0 ?s |- _] => rename s into u end. 
grab contains; rewrite instantiate_quantification.
(have : n + 0 = n by omega) => ->.
(*have : n + 0 = n by omega.*)
simpl.
case /IH; first (apply : Lc.instantiate_pred; assumption).
move => f [H21 [H221 H222]].

(*pose f' m := if Nat.eq_dec m n then s0 else f m.*)
(*pose f' m := if Nat.compare m n is Eq then s0 else f m.*)

exists (fun m => if m =? n then Some u else f m).
subst.
split.

apply : instantiate_prenex_after_instantiate => //.
split => m.

have H' : m < 1 + n -> m = n \/ m < n by omega.
case /H' {H'}; intros; inspect_eqb; [exists u | ]; auto.

(*case m > n*) 
intros. have : n <= m by omega.
inspect_eqb; auto.
Qed.


Lemma contains_prenex_instantiation : forall (f : nat -> option formula) (n : nat) (t : formula), 
  lc n t ->
  (forall (m : nat), m < n -> exists (s : formula), f m = Some s /\ lc 0 s) -> 
  contains (quantify_formula n t) (instantiate_prenex f t).
Proof.
move => f. elim.
(*base case n = 0*)
intros.
rewrite -> (Lc.instantiate_prenex_eq (n:=0)); 
  [constructor | assumption | intros; omega].
(*inductive case n > 0*)
move => n IH t ? Hf.
move /(_ n ltac:(omega)) : (Hf) => [s [Hfn Hs]].
cbn.
apply : contains_trans; first eassumption.
rewrite instantiate_quantification.
(have : n + 0 = n by omega) => ->.
have ? : lc n (instantiate s n t) by apply : Lc.instantiate_pred; auto.
have := @instantiate_prenex_after_instantiate t s n f f Hs.
nip.
move => n'; have := Nat.eq_dec n' n; case => ?; inspect_eqb; subst; auto.
move => <-.
apply : IH; auto.
Qed.


Fixpoint formula_label_bound (s : formula) : nat :=
  match s with
  | (var n) => 0
  | (atom (x, y)) => 1 + y
  | (arr t u) => 1 + (formula_label_bound t) + (formula_label_bound u)
  | (quant t) => 1 + (formula_label_bound t)
  end.

Lemma fresh_in_quantified : forall (n : nat) (a : label) (s : formula), fresh_in a s -> fresh_in a (quantify_formula n s).
Proof.
elim; eauto using fresh_in.
Qed.

(*try to assert freshness in a given type*)
Ltac inspect_freshness := do ? (do [constructor | case; omega | apply : fresh_in_quantified]).


Lemma exists_fresh : forall (formulae : list formula), 
  exists (a : label), Forall (fresh_in a) formulae.
Proof.
move => formulae.

have n := 0.
exists (4, (fold_left Nat.add (map formula_label_bound formulae) n)).
elim : formulae n.
auto.

move => s formulae IH n.
cbn.
constructor; last auto.
clear.

elim : s n; cbn.
(*case var*) eauto using fresh_in.
(*case atom*)

move => a n.
apply fresh_in_atom.
rewrite -> (surjective_pairing a).
case => _.
have := @fold_sum_gt (map formula_label_bound formulae) (n + S (snd a)) (snd a).
lia.

(*case arr*)
move => s ? t ? n.
apply fresh_in_arr.
have : (n + S (formula_label_bound s + formula_label_bound t)) = 
((1 + n + formula_label_bound t) + (formula_label_bound s)) by omega.
move => ->; auto.
have : (n + S (formula_label_bound s + formula_label_bound t)) = 
((1 + n + formula_label_bound s) + (formula_label_bound t)) by omega.
move => ->; auto.

(*case quant*)
move => s ? n.
apply : fresh_in_quant.
have : (n + S (formula_label_bound s)) = 
(1 + n + (formula_label_bound s)) by omega.
move => ->; auto.
Qed.


Lemma substitute_instantiation : forall (t s : formula) (a b : label) (n : nat),
  instantiate (substitute_label a b s) n (substitute_label a b t) = substitute_label a b (instantiate s n t).
Proof.
elim; cbn.
move => n ? ? ? n' *; case : (n' =? n) => //.
move => c ? a *; case : (Label.eqb a c) => //.
all : cbn; intros; f_equal; eauto.
Qed.

Lemma lc_substitute : forall (s : formula) (a b : label) (n : nat), 
  lc n s -> lc n (substitute_label a b s).
Proof.
elim; cbn.
(*case var*) auto.
(*case atom*) intros; rewrite if_fun; constructor.
(*case arr/quant*)
all : intros; grab lc; inversion; eauto using lc.
Qed.

Lemma rename_instantiation : forall (s : formula) (n : nat) (a b : label),
  fresh_in a s -> substitute_label a b (instantiate (atom a) n s) = instantiate (atom b) n s.
Proof.
elim; cbn.
intros.
case : (n0 =? n); cbn; try (rewrite -> (iffRL (Label.eqb_eq _ _))); auto.

all: intros; grab fresh_in; inversion.

rewrite -> Label.neq_neqb; auto.

all: f_equal; auto.
Qed.

Lemma instantiate_renaming_eq : forall (t : formula) (a b c : label) (n : nat), 
  c <> a -> c <> b -> fresh_in c t ->
  (instantiate (atom a) n (substitute_label a b t)) = substitute_label c a (substitute_label a b (instantiate (atom c) n t)).
Proof.
elim; cbn.

(*case var*)
intros.
case : (Nat.eq_dec n n0); cbn; intros; inspect_eqb; cbn => //.
rewrite -> Label.neq_neqb; auto.
cbn. rewrite -> (iffRL (Label.eqb_eq _ _)); auto.

(*case atom*)
intros.
cbn.
rewrite if_fun.
cbn.
grab fresh_in; inversion.
case : (Label.eqb a l); rewrite -> Label.neq_neqb; auto.

(*case arr*)
intros.
grab shape (fresh_in c (arr _ _)); inversion.
cbn; f_equal; eauto.

(*case quant*)
intros.
grab shape (fresh_in c (quant _)); inversion.
cbn; f_equal; eauto.
Qed.

(*auxiliary predicate for induction on depth*)
Inductive contains_depth : nat -> formula → formula → Prop :=
  | contains_depth_rfl : ∀ (s: formula), contains_depth 0 s s
  | contains_depth_trans : ∀ (n : nat) (s t u: formula), lc 0 s → contains_depth n (instantiate s 0 u) t → contains_depth (1+n) (quant u) t.

Lemma contains_exists_depth : forall s t, contains s t -> exists n, contains_depth n s t.
Proof.
move => s t.
elim.

intros.
exists 0.
constructor.

intros.
move : H1 => [n H'].
exists (1+n).
eauto using contains_depth.
Qed.

Lemma contains_erase_depth : forall s t n, contains_depth n s t -> contains s t.
Proof.
intros *.
elim; eauto using contains.
Qed.

Lemma substitute_contains : forall (s t : formula) (a b: label), 
  contains s t -> contains (substitute_label a b s) (substitute_label a b t).
Proof.
intros *.
move /contains_exists_depth => [n ?].
grab contains_depth. do 2 (grab formula). grab nat.
elim.
intros; grab contains_depth; inversion; eauto using contains.

intros * => IH.
intros *; inversion.
cbn.
grab lc. move /(lc_substitute a b) => ?.
apply : contains_trans.
eassumption.
rewrite substitute_instantiation.
apply : (IH).
assumption.
Qed.

Lemma instantiate_renaming_neq : forall (s : formula) (n : nat) (a b c : label), a <> c -> 
  instantiate (atom c) n (substitute_label a b s) = substitute_label a b (instantiate (atom c) n s).
Proof.
elim; cbn.
(*case var*)
move => n n' *.
case : (n' =? n) => //.
cbn; rewrite -> Label.neq_neqb => //.

(*case atom*) move => d ? a *; case : (Label.eqb a d ) => //.
(*case arr/quant*) all: intros; f_equal; auto.
Qed.

Lemma substitute_chain : forall (s : formula) (params : list formula) (a b c : label), 
  chain s c params -> chain (substitute_label a b s) (if Label.eqb a c then b else c) (map (substitute_label a b) params).
Proof.
intros *.
elim; cbn; intros.

constructor.
grab contains; move /(substitute_contains a b).
rewrite <- if_fun.
apply.

apply : (chain_cons (u := substitute_label a b u)).
grab contains; apply /(substitute_contains a b).
assumption.
Qed.

Lemma substitute_fresh_label : forall (s : formula) (a b : label), 
  fresh_in a s -> s = substitute_label a b s.
Proof.
elim; cbn.
auto.
all : intros; grab fresh_in; inversion; (try (f_equal; auto)).
rewrite -> Label.neq_neqb => //.
Qed.

Lemma map_substitute_fresh_label : forall (a b : label) (Γ : list formula), Forall (fresh_in a) Γ -> Γ = (map (substitute_label a b) Γ).
Proof.
move => a b.
elim => //.
cbn.
intros.
have ? := substitute_fresh_label.
decompose_Forall.
f_equal; auto.
Qed.


Lemma bind_instantiate : forall (a : label) (t : formula) (n : nat), fresh_in a t -> bind a n (instantiate (atom a) n t) = t.
Proof.
move => a. elim => /=.
move => m n _. have : (n = m) \/ (n <> m) by lia. case => ?; inspect_eqb => //=.
have := Label.eqb_eq a a. subst. by move /iffRL => ->.
move => b ?. inversion. by rewrite Label.neq_neqb.
move => *. grab fresh_in. inversion. f_equal; auto.
move => *. grab fresh_in. inversion. f_equal; auto.
Qed.
