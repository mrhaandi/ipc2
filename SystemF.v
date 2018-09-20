Require Import Utf8.

Require Import FormulaFacts.
Require Import List.
Require Import Omega.
Import ListNotations.
Require Import ListFacts.

Require Import UserTactics.
Require Import MiscFacts.

From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Term.
Require Import Derivations.

(*additional lemmas*)
Lemma lc_bind : forall (M : term) (n : nat) (x : label), Term.lc n M -> Term.lc (S n) (Term.bind x n M).
Proof.
elim; cbn.
move => y; intros; case : (Label.eqb x y); constructor; omega.
all: intros; gimme Term.lc; inversion; constructor; auto + omega.
Qed.

Definition environment : Set := list (label * formula).

Definition fresh_term_label (x : label) (Γ : environment) := Forall (fun '(y, _) => x <> y) Γ.

Definition fresh_formula_label (a : label) (Γ : environment) := Forall (fun '(_, t) => fresh_in a t) Γ.


(*s is well formed, if it contains no unbound De Bruijn indices*)
Inductive well_formed_formula (s : formula) : Prop :=
  | wff_lc : lc 0 s -> well_formed_formula s.

(*Γ is well formed, if any term variable appears at most once*)
Inductive well_formed_environment : environment -> Prop :=
  | wfe_nil : well_formed_environment nil
  | wfe_cons : forall (x : label) (s : formula) (Γ : environment), 
    well_formed_formula s -> well_formed_environment Γ -> fresh_term_label x Γ -> well_formed_environment ((x, s) :: Γ).

(*M is well formed, if it contains no unbound De Bruijn indices*)
Inductive well_formed_term (M : term) : Prop :=
  | wft_lc : Term.lc 0 M -> well_formed_term M.


Inductive f_derivation (Γ: environment) : term -> formula -> Prop :=
  | f_ax : forall (x : label) (s: formula), well_formed_environment Γ -> 
    In (x, s) Γ -> f_derivation Γ (free_var x) s
  | f_elim_arr : forall (M N : term) (s t : formula), 
    f_derivation Γ M (Formula.arr s t) -> f_derivation Γ N s -> f_derivation Γ (term_app M N) t
  | f_intro_arr : forall (x : label) (s t : formula) (M : term), 
    f_derivation ((x, s) :: Γ) M t -> f_derivation Γ (term_abs (Term.bind x 0 M)) (arr s t)
  | f_elim_quant : forall (M : term) (s t : formula), 
    f_derivation Γ M (quant s) -> well_formed_formula t -> f_derivation Γ M (instantiate t 0 s)
  | f_intro_quant : forall (M : term) (a : label) (s: formula), 
    fresh_formula_label a Γ -> f_derivation Γ M s -> f_derivation Γ M (quant (Formula.bind a 0 s)).


Lemma f_derivation_wft : forall (Γ : environment) (M : term) (t : formula), 
  f_derivation Γ M t -> well_formed_term M.
Proof.
intros until 0; elim => //.

intros; do ? constructor.

intros; do 2 (gimme well_formed_term; inversion); by do 2 constructor.

intros; gimme well_formed_term; inversion; do 2 constructor.
by apply : lc_bind.
Qed.

Lemma f_derivation_wfe : forall (Γ : environment) (M : term) (t : formula), 
  f_derivation Γ M t -> well_formed_environment Γ.
Proof.
intros until 0; elim => //.
intros; gimme well_formed_environment; by inversion.
Qed.

Lemma f_derivation_wff : forall (Γ : environment) (M : term) (t : formula), 
  f_derivation Γ M t -> well_formed_formula t.
Proof.
intros until 0; elim => //.
(*should be doable*)
Admitted.


Inductive derivation2 : nat -> environment -> term -> formula → Prop :=
  | ax : forall (n : nat) (Γ : environment) (x : label) (s: formula), 
    In (x, s) Γ -> derivation2 n Γ (free_var x) s
  | elim_arr : forall (n : nat) (Γ : environment) (M N : term) (s t : formula), 
    derivation2 n Γ M (arr s t) -> derivation2 n Γ N s -> derivation2 (S n) Γ (term_app M N) t
  | intro_arr : forall (n : nat) (Γ : environment) (M : term) (s t : formula), 
    (forall (x : label), derivation2 n ((x, s) :: Γ) (Term.instantiate x 0 M) t) -> derivation2 (S n) Γ (term_abs M) (arr s t)
  | elim_quant : forall (n : nat) (Γ : environment) (M : term) (s t : formula), 
    derivation2 n Γ M (quant s) -> lc 0 t -> derivation2 (S n) Γ M (instantiate t 0 s)
  | intro_quant : forall (n : nat) (Γ : environment) (M : term) (s : formula), 
    (forall (a: label), derivation2 n Γ M (instantiate (atom a) 0 s)) -> derivation2 (S n) Γ M (quant s).

(*chain s a params morally means that s can be instanciated as p1 -> ... -> pn -> a*)
Inductive partial_chain (s t : formula) : list formula -> Prop :=
  | partial_chain_nil : contains s t -> partial_chain s t List.nil
  | partial_chain_cons : forall (s' t': formula) (ts: list formula), contains s (arr s' t') -> partial_chain t' t ts -> partial_chain s t (s' :: ts).

(*
Inductive derivation3 : nat -> list formula -> formula → Prop :=
  | ax3 : forall (n : nat) (Γ : list formula) (s t: formula) (ts : list formula), 
    Forall well_formed_formula Γ ->
    In s Γ -> partial_chain s t ts -> Forall (derivation3 n Γ) ts ->
    derivation3 (S n) Γ s
  | intro_arr3 : forall (n : nat) (Γ : list formula) (s t : formula), 
    derivation3 n (s :: Γ) t -> derivation3 (S n) Γ (arr s t)
  | intro_quant3 : forall (n : nat) (Γ : list formula) (s : formula), 
   (forall (a: label), derivation3 n Γ (instantiate (atom a) 0 s)) -> derivation3 (S n) Γ (quant s).


Lemma prerequisive : forall (n : nat) (Γ : list formula) (s t : formula), 
  Forall well_formed_formula Γ -> well_formed_formula (quant s) -> 
  derivation3 n Γ (quant s) -> 
  exists n, normal_derivation n Γ (instantiate t 0 s).
Proof.
elim /lt_wf_ind.
move => n IH.
intros.
gimme derivation3; inversion.
admit.
Admitted.
*)
Lemma exists_partial_chain : forall (n : nat) (Γ : environment) (M : term) (t : formula),
  head_form M -> derivation2 n Γ M t -> 
  exists (s : formula) (ts : list formula), 
    In s (map snd Γ) /\ 
    partial_chain s t ts /\ 
    Forall (fun t => exists (n : nat) (M : term), derivation2 n Γ M t) ts.
Proof.
intros until 0 => H.
move : n Γ t.
elim : H.

admit. (*probably induction*)




{ (*case x*)
intros until 0; inversion.
eexists; exists [].
do_last 2 split.
rewrite in_map_iff.
eauto.
do 2 constructor.
constructor.



Qed.






Lemma bind_normal_and_head : forall (x : label) (N : term) (n : nat), 
  (normal_form (Term.bind x n N) -> normal_form N) /\ (head_form (Term.bind x n N) -> head_form N).
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

Lemma bind_normal : forall (x : label) (N : term) (n : nat), normal_form (Term.bind x n N) <-> normal_form N.
Proof.
firstorder using bind_normal_and_head, Term.normal_bind.
Qed.


Tactic Notation "move" "//" := let H := fresh in move => H; move /(H); clear H.


Fixpoint formula_size (t : formula) :=
  match t with
  | (var _) => 1
  | (atom _) => 1
  | (arr s t) => 1+(formula_size s)+(formula_size t)
  | (quant s) => 1+(formula_size s)
  end.

Lemma normal_derivation_exists_quant : forall (Γ : list formula) (s : formula),
  (forall (a : label), exists (n : nat), normal_derivation n Γ (instantiate (atom a) 0 s)) ->
  exists (n : nat), normal_derivation n Γ (quant s).
Proof.
intros until 0 => H.
have [a ?] := exists_fresh (s :: Γ).
decompose_Forall.
gimme where normal_derivation. move /(_ a) => [n ?].
exists (S n). constructor. move => b.
gimme normal_derivation.
move /substitute_normal_derivation. move /(_ a b).
rewrite rename_instantiation; first done.
rewrite <- map_substitute_fresh_label; last done.
apply.
Qed.


Lemma contains_transitivity : forall s t u, contains s t -> contains t u -> contains s u.
Proof.
intros until 0; elim => //.
intros; apply : contains_trans; eauto.
Qed.


Lemma instantiate_partial_chain : forall a s t ts, partial_chain s (quant t) ts -> partial_chain s (instantiate (atom a) 0 t) ts.
Proof.
intros until 0.
elim : ts s t.

move => s t. inversion. constructor.
gimme contains. move /contains_transitivity.
apply.
apply : contains_trans; last constructor. constructor.

move => t ts IH.
move => s' t'. inversion.
apply : partial_chain_cons; first eassumption.
by apply : IH.
Qed.


Lemma formula_size_instantiate_atom : forall a s n, formula_size (instantiate (atom a) n s) = formula_size s.
Proof.
intro.
elim; cbn => //.
move => n m.
case : (m =? n); done.

all: intros; eauto.
Qed.


Lemma partial_chain_arr : forall ts s t u, partial_chain s (arr t u) ts -> partial_chain s u (ts ++ [t]).
Proof.
elim.
intros until 0; inversion.
apply : partial_chain_cons; try eassumption + constructor.
constructor.

move => t' ts IH.
intros until 0; inversion.
apply : partial_chain_cons; try eassumption.
by apply IH.
Qed.

Lemma contains_wff : forall s t, well_formed_formula s -> contains s t -> well_formed_formula t.
Proof.
(*doable*)
Admitted.


Lemma partial_chain_wff : forall ts s t, well_formed_formula s -> partial_chain s t ts -> well_formed_formula t.
Proof.
elim.
intros. gimme partial_chain. inversion.
apply : contains_wff; eassumption.

move => u ts IH.
intros. gimme partial_chain. inversion.
apply : IH; last eassumption.
gimme contains. move /contains_wff.
nip; first auto. inversion. gimme lc. inversion.
by constructor.
Qed.

Lemma partial_chain_atom : forall a ts s, partial_chain s (atom a) ts -> chain s a ts.
Proof.
move => a; elim.
intros until 0. inversion. by constructor.

move => t ts IH s.
inversion. apply : chain_cons; eauto.
Qed.

Lemma relax_depth_normal_derivation : forall (n m : nat) (Γ : list formula) (s : formula), 
  normal_derivation n Γ s → n <= m -> normal_derivation m Γ s.
Proof.
elim /lt_wf_ind.
move => n IH. intros.
gimme normal_derivation. inversion.

all: have : m = S (Nat.pred m) by omega.
all: move => ->.

constructor.
apply : IH; try eassumption; omega.

constructor.
move => a. gimme where normal_derivation. move /(_ a) => ?.
apply : IH; try eassumption; omega.

apply : derive_atom; try eassumption.
apply : Forall_impl; last eassumption.
intros. apply : IH; try eassumption; omega.
Qed.


(*shown*)
Lemma eta_longness : forall (Γ : list formula) (s t : formula) (ts : list formula), 
  Forall well_formed_formula Γ -> In s Γ -> partial_chain s t ts -> 
  Forall (fun t => exists (n : nat), normal_derivation n Γ t) ts -> exists (n : nat), normal_derivation n Γ t.
Proof.
move => Γ s t.
move H : (formula_size t) => n.
elim /lt_wf_ind : n Γ s t H.
move => n IH Γ s. case.

{ (*case var, contradiction*)
intros until 0 => ? ?.
intros. gimme partial_chain. move /partial_chain_wff.
nip. 
gimme In. gimme Forall where well_formed_formula.
rewrite Forall_forall. by move //.
inversion. gimme lc. inversion. omega.
}

{(*case atom*)
intros.
gimme In.
gimme Forall.
move /Forall_exists_monotone.
nip.
intros. apply : relax_depth_normal_derivation; eassumption.
move => [n'].

gimme partial_chain. move /partial_chain_atom. move /derive_atom.
do 2 move //.
eauto.
}

{ (*case arr*)
move => s' t'; cbn => ?.
intros.

have ? : well_formed_formula s'.
gimme partial_chain. move /partial_chain_wff.
nip. 
gimme In.
gimme Forall where well_formed_formula.
rewrite Forall_forall. by move //.
inversion. gimme lc. inversion. by constructor.

gimme partial_chain. move /partial_chain_arr.

gimme In. move /(@in_cons formula s').
move : (IH). move //. move //.
move /(_ _ _ ltac:(reflexivity)).
nip; first omega.
nip. constructor; auto.

nip. 
rewrite Forall_app. split.
apply : Forall_impl; last eassumption.
cbn. move => u [n' ?]. exists n'.
gimme normal_derivation. apply /normal_weakening.
intros. by apply in_cons.

constructor; last done.
have : partial_chain s' s' [] by do 2 constructor.
move /IH. apply; try (by constructor). omega.

move => [n' ?].
exists (S n').
by apply : derive_arr. 
}

{ (*case quant*)
cbn => s'; intros.
apply normal_derivation_exists_quant => a.
apply : IH; try eassumption + reflexivity.
rewrite formula_size_instantiate_atom; omega.
gimme partial_chain. apply /instantiate_partial_chain.
}
Qed.


(*repeated instantiation by locally closed formulae*)
Inductive contains_depth : nat -> formula -> formula -> Prop :=
  | contains_depth_rfl : forall (s: formula), contains_depth 0 s s
  | contains_depth_trans : forall (n : nat) (s t u: formula), lc 0 s -> contains_depth n (instantiate s 0 u) t -> contains_depth (S n) (quant u) t.

(*replace all occurrences of a in s by t*)
Fixpoint substitute (a : label) (s t : formula) : formula :=
  match t with
    | (atom b) => if Label.eqb a b then s else t
    | (var _) => t
    | (arr s' t') => arr (substitute a s s') (substitute a s t')
    | (quant t') => quant (substitute a s t')
  end.

Lemma eqb_eq' : forall (a b : label), a = b -> (Label.eqb a b = true).
Proof.
intros.
by apply (Label.eqb_eq a b).
Qed.

(*MOST IMPORTANT LEMMA*)
Lemma prerequisive0 : forall (a : label) (s : formula), lc 0 s -> forall (n : nat) (Γ : list formula) (t : formula), 
  normal_derivation n Γ t -> ∃ n : nat, normal_derivation n (map (substitute a s) Γ) (substitute a s t).
Proof.
move => a s ?.
elim /lt_wf_ind; cbn.
move => n IH; intros.
gimme normal_derivation; inversion.

{
gimme normal_derivation; move /IH.
move /(_ ltac:(omega)) => [n ?].
exists (S n). cbn. by constructor.
}

{
admit. (*exchange forall exists*)
}

{
cbn.
match goal with [_ : chain _ ?a' _ |- _] => rename a' into b end.
case : (Label.eq_dec a b).
intro. subst. rewrite eqb_eq'; first done.
(*needs partial chain derivations*)
admit. (*???*)

Admitted.

Lemma prerequisive : forall (n : nat) (Γ : list formula) (s t : formula), Forall well_formed_formula Γ -> well_formed_formula (quant s) -> 
  normal_derivation n Γ (quant s) -> 
  exists n, normal_derivation n Γ (instantiate t 0 s).
Proof.
intros.
gimme normal_derivation; inversion.
have := exists_fresh (s :: t :: Γ) => [[a ?]].
decompose_Forall.
gimme where normal_derivation. move /(_ a).
revert dependent a => a.
revert dependent Γ.

Admitted.

(*key lemma*)
Lemma eta_longness2 : forall (m n : nat) (Γ : list formula) (s t : formula), 
  Forall well_formed_formula Γ -> well_formed_formula s -> well_formed_formula t -> normal_derivation n Γ s -> contains_depth m s t -> 
  exists (n : nat), normal_derivation n Γ t.
Proof.
elim /lt_wf_ind.
move => m IH.
intros; gimme contains_depth; inversion.
eauto.

gimme normal_derivation; inversion.
gimme contains_depth; move /IH.
nip; first omega.
apply; try eassumption.
admit. (*easy*)

Admitted.


Lemma wfe_wff : forall (Γ : environment), well_formed_environment Γ -> Forall well_formed_formula (map snd Γ).
Proof.
elim; cbn.

intros. by constructor.

move => [? s] Γ IH.
inversion.
constructor; eauto.
Qed.


Lemma instantiate_bind : forall a b s n, lc n s -> (instantiate (atom b) n (Formula.bind a n s)) = substitute_label a b s.
Proof.
move => a b. elim; cbn.

intros. gimme lc. inversion. by inspect_eqb.

move => c ? ?.
case : (Formula.Label.eqb a c); cbn; by inspect_eqb.

all: intros; gimme lc; inversion; f_equal; eauto.
Qed.


Lemma fresh_formula_label_Forall : forall a Γ, fresh_formula_label a Γ -> Forall (fresh_in a) (map snd Γ).
Proof.
move => a. elim.
intros. constructor.

move => [? s] Γ IH. inversion.
constructor; eauto.
Qed.

(*TODO, main lemma*)
Lemma f_derivation_soundness : forall (Γ : environment) (M : term) (t : formula), 
  f_derivation Γ M t -> normal_form M -> exists (n : nat), normal_derivation n (map snd Γ) t.
Proof.
intros until 0; elim; clear.

{ (*case free_var*)
intros.
gimme In. move /(in_map snd). cbn.
move /eta_longness. apply.
by apply : wfe_wff.
do 2 constructor.
constructor.
}

{ (*case app*)
intros; gimme normal_form; inversion; gimme head_form; inversion.
admit.
}

{ (*case abs*)
intros; gimme normal_form; inversion.
gimme head_form; inversion.
gimme normal_form. move /bind_normal.
gimme where normal_derivation. move //.
move => [?]; cbn => ?.
eexists; apply : derive_arr; eassumption.
}

{(*case inst*)
intros.
gimme where normal_derivation. move /(_ ltac:(assumption)) => [? ?].
apply : eta_longness2. (*only contains is used*)
admit.
eassumption.
admit.
admit.
admit.
}

{ (*case gen*)
intros.
apply : normal_derivation_exists_quant => b.
rewrite instantiate_bind.
gimme f_derivation. move /f_derivation_wff.
by inversion.

gimme where normal_derivation. nip; first auto.
move => [n]. move /(substitute_normal_derivation a b).
rewrite <- map_substitute_fresh_label; last by apply fresh_formula_label_Forall.
eauto.
}
Qed.

head_form M
normal_form N

Inductive normal_derivation : nat -> list formula -> formula -> Prop :=
(*(s :: Γ) in derive_arr not a problem, context permutation is admissible, think bottom-up*)
  | derive_arr : forall (n : nat) (Γ: list formula) (s t: formula), 
    normal_derivation n (s :: Γ) t -> normal_derivation (S n) Γ (Formula.arr s t)
  | derive_quant : forall (n : nat) (Γ: list formula) (s: formula), 
   (forall (a: label), normal_derivation n Γ (instantiate (atom a) 0 s) ) -> normal_derivation (S n) Γ (Formula.quant s)
(* | derive_atom : forall (n : nat) (Γ: list formula) (a: label) (s: formula) (params: list formula), 
      In s Γ -> Formula.chain s params a -> (Forall (normal_derivation n Γ) (params)) -> normal_derivation (if params is nil then n else S n) Γ (Formula.atom a).*)
  | derive_atom : forall (n : nat) (Γ: list formula) (a: label) (s: formula) (params: list formula), 
      In s Γ -> Formula.chain s a params -> (Forall (normal_derivation (Nat.pred n) Γ) (params)) -> (n <> 0 \/ params = nil) -> normal_derivation n Γ (Formula.atom a).

Conjecture normalization : forall (Γ: list formula) (s: formula), derivation Γ s -> exists (n : nat), normal_derivation n Γ s.

(*tries to solve derivation Γ s automatically*)
Ltac derivation_rule := first
  [ apply ax => //; by list_element
  | ( do ? (apply intro_quant => //=; intro);
      do ? (apply intro_arr);
      apply ax => //; by list_element)
  | match goal with | [H : In ?s ?Γ |- derivation _ ?s] => apply ax; list_inclusion end
  | (by (eauto using derivation))].


Theorem conservativity : forall (n : nat) (Γ: list formula) (s: formula), normal_derivation n Γ s -> derivation Γ s.
Proof.
elim; intros until 0.

(*base case n = 0*)
inversion. intuition. subst.
gimme chain; inversion; derivation_rule.

(*inductive case n > 0*)
move => IH Γ *.
gimme normal_derivation; inversion; auto using intro_arr, intro_quant.

(*atom case*)
gimme In; move /ax.
gimme Forall;
gimme chain; elim.
(*one step chain*) derivation_rule.
(*multistep chain*) move => ? ? t u *.
decompose_Forall.

have ? : derivation Γ u by derivation_rule.
auto.
Qed.

(*inversion lemmas*)
Lemma inv_arr : forall (Γ : list formula) (s t : formula),
  derivation Γ (arr s t) -> derivation (s :: Γ) t.
Proof.
intros until 0.
move /normalization => [? H].
inversion_clear H.
apply: conservativity; eassumption.
Qed.

Lemma inv_atom : forall (Γ : list formula) (a : label), derivation Γ (atom a) -> 
  exists (s : formula) (params : list formula), In s Γ /\ chain s a params /\ (Forall (derivation Γ) (params)).
Proof.
intros until 0.
move /normalization => [? H].
inversion_clear H.
match goal with | [H : Forall _ _ |- _] => eapply Forall_impl in H; first last end.
intros.
eapply conservativity. eassumption.
exists s, params. auto.
Qed.

Lemma inv_normal_quant : forall (n : nat) (Γ: list formula) (s : formula), normal_derivation n Γ (quant s) ->
  exists (m : nat), n = S m /\ (forall (a: label), normal_derivation m Γ (instantiate (atom a) 0 s)).
Proof.
intros until 0 => H.
inversion_clear H.
eexists; split; [reflexivity | assumption].
Qed.

Lemma inv_quant : forall (Γ: list formula) (s : formula), derivation Γ (quant s) ->
  (forall (a: label), derivation Γ (instantiate (atom a) 0 s)).
Proof.
intros until 0.
move /normalization => [n HD].
move /inv_normal_quant : HD => [m [? ?]].
eauto using conservativity.
Qed.

Lemma inv_normal_arr : forall (n : nat) (Γ: list formula) (s t : formula), normal_derivation n Γ (arr s t) ->
  exists (m : nat), n = S m /\ normal_derivation m (s :: Γ) t.
Proof.
intros until 0 => H.
inversion_clear H.
eexists; split; [reflexivity | assumption].
Qed.

(*decomposition tactics*)
Ltac decompose_normal_derivation := 
  do ? (
  lazymatch goal with
  | [H : Forall _ (_ :: _) |- _] => inversion_clear H
  | [H : Forall _ nil |- _] => inversion_clear H
  | [H : normal_derivation _ _ (quant _) |- _ ] => 
    let n := fresh "n" in move /inv_normal_quant : H => [n [? H]]
  | [H : normal_derivation _ _ (arr _ _) |- _ ] => 
    let n := fresh "n" in move /inv_normal_arr : H => [n [? H]]
  | [H : normal_derivation _ _ _ |- _] => inversion_clear H
  end).

Ltac decompose_chain :=
  do ? (
  match goal with
  | [H : chain ?s _ _ |- _] =>
    match eval hnf in s with
    | arr _ _ => (move /chain_arr : H => [? [? H]]); subst
    | atom _ => (move /chain_atom : H => [? ?]); try done; subst
    end
  end).

Ltac decompose_derivation := 
  do ? (
  match goal with
  | [H : derivation _ ?s |- _] => 
    match eval hnf in s with
    | arr _ _ => move /inv_arr : H => H
    | atom _ => 
      let s := fresh in 
      let H' := fresh in
      move /inv_atom : H => [s [? [H' [? ?]]]]
    end
  end).

Ltac decompose_contains :=
  match goal with
  | [H : contains _ _ |- _] => inversion_clear H
  end.


Ltac decompose_lc := 
  do ? (
  match goal with
  | [H : lc _ ?s |- _] => 
    match eval hnf in s with
    | arr _ _ => inversion_clear H
    | var _ => inversion_clear H
    | atom _ => inversion_clear H
    end
  end).

Tactic Notation "gimme" "where" constr(p) := 
  lazymatch goal with
  | [H : context[p] |- _] => move : H
  end.

Lemma substitute_normal_derivation : forall (n : nat) (s : formula) (Γ : list formula) (a b : label), 
  normal_derivation n Γ s -> normal_derivation n (map (substitute_label a b) Γ) (substitute_label a b s).
Proof.
move => n; apply (lt_wf_ind n).

intros until 0 => IH; intros.

gimme normal_derivation; inversion; cbn.
(*arr*)
apply : derive_arr.
rewrite <- map_cons.
apply : IH; try done + omega.
(*quant*)
match goal with [_ : context G [instantiate _ _ ?s'] |- _] => rename s' into s end.
apply : derive_quant => c.
case : (Label.eq_dec c a).

intro; subst c.
have [d Hd] := exists_fresh ([atom a; atom b; s] ++ (map (substitute_label a b) Γ)).
decompose_Forall.

do 2 (gimme shape (fresh_in d (atom _)); inversion).
rewrite -> (@instantiate_renaming_eq _ _ _ d); auto.
rewrite -> (@map_substitute_fresh_label d a (map (substitute_label a b) Γ)); auto.

intros.
rewrite -> instantiate_renaming_neq; auto.

(*atom*)
set Γ' := map (substitute_label a b) Γ.
match goal with [_ : In ?s' Γ |- _] => rename s' into s end.
set s' := (substitute_label a b) s.
rewrite if_fun.
match goal with [_ : chain s ?a' params |- _] => rename a' into c end.
set a' := (if Label.eqb a c then b else c).
set params' := map (substitute_label a b) params.
have ? : In s' Γ' by apply : in_map; assumption.
have ? : chain s' a' params' by apply : substitute_chain; assumption.

have ? : Forall (normal_derivation (Nat.pred n0) Γ') params'.
gimme Forall; move : IH; gimme or; clear; revert dependent params.
elim; cbn; first done.

intros; decompose_Forall.
gimme or; case; last done; move => ?.
match goal with [_ : ?n' ≠ 0 |- _] => have ? : Nat.pred n' < n' by omega end.
eauto.

apply : derive_atom; try eassumption.
gimme or; case => ?; last subst params' params; auto.
Qed.


Lemma substitute_derivation_bindable : forall (s : formula) (Γ : list formula) (a b : label), 
  Forall (fresh_in a) Γ -> derivation Γ s -> derivation Γ (substitute_label a b s).
Proof.
intros.
have : Γ = map (substitute_label a b) Γ by apply map_substitute_fresh_label.
move => ->.
gimme derivation; move /normalization => [? ?].
eauto using conservativity, substitute_normal_derivation.
Qed.


(*the usual presentation of intro_quant*)
Theorem intro_quant_fresh : forall (s: formula) (Γ : list formula) (a : label), 
  Forall (fresh_in a) Γ -> fresh_in a s ->
  (derivation Γ (instantiate (atom a) 0 s)) -> derivation Γ (Formula.quant s).
Proof.
move => s Γ a H *.
apply intro_quant => b.
gimme derivation.
move /(substitute_derivation_bindable b H).
rewrite -> rename_instantiation; auto.
Qed.


Lemma normal_weakening : forall (n : nat) (Γ Δ: list formula), 
  (forall (s : formula), In s Γ -> In s Δ) -> forall (t: formula), normal_derivation n Γ t -> normal_derivation n Δ t.
Proof.
elim.
intros until 0 => ? ?; inversion.
intuition; subst.
apply: derive_atom; eauto.

move => n IH Γ Δ H_in t; inversion.
(*case arr*)
apply: derive_arr. apply: IH; try eassumption.
move => s'. move : (H_in s').
list_inclusion.

(*case quant*)
apply: derive_quant. eauto.
(*case atom*)
apply: derive_atom; eauto.
gimme Forall; rewrite -> ? Forall_forall.
eauto.
Qed.


Lemma weakening : forall (Γ Δ: list formula) (t: formula), 
  derivation Γ t -> (forall (s : formula), In s Γ -> In s Δ) -> derivation Δ t.
Proof.
intros until 0.
move /normalization; case.
eauto using conservativity, normal_weakening.
Qed.


Lemma weakening_cons : forall (Γ: list formula) (s t: formula), derivation Γ t -> derivation (s :: Γ) t.
Proof.
firstorder using weakening.
Qed.


Lemma context_generalization : forall (Γ Δ: list formula) (t : formula), 
  derivation Γ t -> (forall (s : formula), In s Γ -> derivation Δ s) -> derivation Δ t.
Proof.
elim.
(*base case*)
intros.
apply: (weakening (Γ := [])) => //.
(*inductive case*)
intros until 0 => IH.
intros until 1 => H'.
have ? : derivation l (arr a t) by derivation_rule.
have ? : derivation Δ (arr a t) => //.
apply IH => //; intros; apply H'; list_inclusion.
have ? : derivation Δ a by apply H'; list_inclusion.
derivation_rule.
Qed.


Lemma context_generalization_app : forall (Γ Δ Γ': list formula) (t : formula), 
  derivation (Γ ++ Δ) t -> (forall (u : formula), In u Γ -> derivation Γ' u) -> derivation (Γ' ++ Δ) t.
Proof.
intros.
apply: (context_generalization). eassumption.
move => s H_In.
apply in_app_or in H_In.
case : H_In => H_In.
apply : (weakening (Γ := Γ')); auto with *.
derivation_rule.
Qed.


(*looks for In/chain statements and eliminates impossible cases*)
Ltac filter_context_chain := 
  let filter_context_chain_inner H_In :=
    move => H_In; subst => //;
    (do ? (
      match goal with 
      | [|- chain ?s _ _ -> _] => 
        match eval hnf in s with
        | (arr _ _) => (let H' := fresh in move /chain_arr => [? [? H']]; move: H'; subst => //)
        | (atom _) => (move /chain_atom => [? ?]; subst => //)
        end
      end))
  in
    match goal with | [ H_In : In ?s _, H_c : chain ?s _ _ |- _] => move: H_In H_c;
    rewrite ? (in_app_iff, in_cons_iff, or_assoc);
    let t := (filter_context_chain_inner H_In) in decompose_or t end.


(*looks for In statements to derive current goal and eliminates trivial cases*)
Ltac filter_context_derivation := 
  let rec filter_context_derivation_inner H_In :=
    move => H_In; subst; try derivation_rule
  in
  match goal with | [ H_In : In ?s _ |- derivation _ ?s] => 
    move: H_In;
    rewrite ? (in_app_iff, in_cons_iff, or_assoc);
    let t := filter_context_derivation_inner H_In in decompose_or t
  end.