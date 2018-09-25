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
Require Import FormulaFacts.

Tactic Notation "move" "//" := 
  let H := fresh in move => H; 
  match goal with 
    | [|- _ -> _] => move /(H) 
    | [|- forall _, _] => let a := fresh in move => a; move : (H a); (try clear a)
  end; clear H.

Tactic Notation "move" "\\" :=
  let H1 := fresh in let H2 := fresh in move => H1 H2; move : H2 H1; move //.


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

Lemma contains_wff : forall s t, contains s t -> well_formed_formula s -> well_formed_formula t.
Proof.
intros until 0. elim.
auto.

intros. gimme well_formed_formula where quant. inversion. gimme lc. inversion.

intros. gimme where well_formed_formula. apply. constructor.
gimme lc. move /Lc.instantiate_pred. by apply. 
Qed.

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

Lemma partial_chain_param_wff : forall ts s t u, well_formed_formula s -> partial_chain s t ts -> In u ts -> well_formed_formula u.
Proof.
elim.
intros. gimme In. inversion.

move => t' ts IH.
intros. gimme partial_chain. inversion.
gimme In. case.

intro. subst.
gimme contains. move /contains_wff.
nip; first auto. inversion. gimme lc. inversion.
by constructor.

gimme partial_chain.
move /IH. move //. apply.
gimme contains. move /contains_wff.
nip; first auto. inversion. gimme lc. inversion.
by constructor.
Qed.



Lemma partial_chain_atom : forall a ts s, partial_chain s (atom a) ts <-> chain s a ts.
Proof.
move => a; elim.
intros until 0.
split; inversion; by constructor.

move => t ts IH s.
split.
inversion. apply : chain_cons.
eassumption. by rewrite <- IH.

inversion. apply : partial_chain_cons.
eassumption. by rewrite -> IH.
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

Lemma substitute_instantiation2 : forall a u, lc 0 u -> forall t s n, 
  substitute a u (instantiate s n t) = instantiate (substitute a u s) n (substitute a u t).
Proof.
move => a u ?.
elim; cbn.
{
move => n s m. case : (m =? n); by cbn.
}
{
move => b s n.
case : (Label.eqb a b); cbn => //.
by rewrite Lc.instantiate_eq0.
}
all : intros; f_equal; eauto.
Qed.


Lemma instantiate_substitution_neq : forall (a b : label) (s t : formula) (n : nat), 
  a <> b -> lc 0 s ->
  (instantiate (atom a) n (substitute b s t)) = substitute b s (instantiate (atom a) n t).
Proof.
intros. elim : t n; cbn.
move => n m. case : (m =? n); cbn => //.
rewrite -> Label.neq_neqb; auto.

move => c n. case : (Label.eqb b c); cbn => //.
by apply Lc.instantiate_eq0.

all: intros; f_equal; auto.
Qed.


Lemma lc_substitute : forall a s t n, lc n s -> lc n t -> lc n (substitute a s t).
Proof.
move => a s. elim; cbn => //.

move => b *. by case : (Label.eqb a b).

intros; constructor; gimme lc where arr; inversion; eauto.

intros; constructor; gimme lc where quant; inversion.
gimme lc where S. gimme where substitute. move //.
nip. apply : Lc.relax; first eassumption; omega.
done.
Qed.


Lemma substitute_contains : forall a s t u, 
  lc 0 u -> contains s t -> contains (substitute a u s) (substitute a u t).
Proof.
intros until 0 => ?. 
elim.
intros. constructor.

intros. cbn. 
apply : contains_trans; first last.

rewrite <- substitute_instantiation2; eassumption.
by apply lc_substitute.
Qed.


Lemma substitute_partial_chain : forall a s t u ts, lc 0 u ->
  partial_chain s t ts -> partial_chain (substitute a u s) (substitute a u t) (map (substitute a u) ts).
Proof.
intros until 0 => ?; elim.
intros. constructor. by apply substitute_contains.
intros. cbn. apply : partial_chain_cons; last eassumption.
gimme contains. by apply /substitute_contains.
Qed.

(*the usual presentation of intro_quant*)
Lemma normal_intro_quant_fresh : forall (s: formula) (Γ : list formula) (a : label) (n : nat), 
  Forall (fresh_in a) Γ -> fresh_in a s ->
  normal_derivation n Γ (instantiate (atom a) 0 s) -> normal_derivation (S n) Γ (Formula.quant s).
Proof.
move => s Γ a n H *.
constructor => b.
gimme normal_derivation. move /(substitute_normal_derivation a b).
rewrite rename_instantiation. done.
rewrite <- map_substitute_fresh_label.
apply. done.
Qed.

Lemma normal_intro_quant_fresh_exists : forall (s: formula) (Γ : list formula) (a : label), 
  Forall (fresh_in a) Γ -> fresh_in a s ->
  (exists (n : nat), normal_derivation n Γ (instantiate (atom a) 0 s)) -> exists (n : nat), normal_derivation (S n) Γ (Formula.quant s).
Proof.
firstorder (eauto using normal_intro_quant_fresh).
Qed.


Lemma fresh_in_substitute : forall a b s t, fresh_in a s -> fresh_in a t -> fresh_in a (substitute b s t).
Proof.
move => a b s. elim; cbn.

intros. constructor.

move => c *. by case : (Label.eqb b c).

intros. gimme fresh_in where arr. inversion. constructor; auto.

intros. gimme fresh_in where quant. inversion. constructor; auto.
Qed.

(*reverts assumption with head p*)
Tactic Notation "gimme" "(" constr(p) ")" :=
  lazymatch goal with 
  | [ H : p _ _ _ _ _ _ _  |- _] => move : (H)
  | [ H : p _ _ _ _ _ _  |- _] => move : (H)
  | [ H : p _ _ _ _ _  |- _] => move : (H)
  | [ H : p _ _ _ _  |- _] => move : (H)
  | [ H : p _ _ _  |- _] => move : (H)
  | [ H : p _ _  |- _] => move : (H)
  | [ H : p _  |- _] => move : (H)
  | [ H : p  |- _] => move : (H)
  end.


(*MOST IMPORTANT LEMMA, old substitute_normal_derivation is only on label basis*)
Lemma substitute_normal_derivation2 : forall (a : label) (s : formula), lc 0 s -> forall (n : nat) (Γ : list formula) (t : formula), 
  normal_derivation n Γ t -> well_formed_formula t -> Forall well_formed_formula Γ -> ∃ n : nat, normal_derivation n (map (substitute a s) Γ) (substitute a s t).
Proof.
move => a s ?.
elim /lt_wf_ind; cbn.
move => n IH; intros.
gimme normal_derivation; inversion.

{
gimme normal_derivation; move /IH.
move /(_ ltac:(omega)).
gimme well_formed_formula. inversion. gimme lc. inversion.
nip. by constructor.
nip. by constructor.
move => [n ?].
exists (S n). cbn. by constructor.
}

{
cbn.
match goal with [_ : well_formed_formula (quant ?s) |- _] => rename s into s' end.
have [b ?] := exists_fresh ((atom a) :: s' :: s :: Γ).
decompose_Forall.
gimme where normal_derivation. move /(_ b).
move /IH. nip. omega.
nip. constructor. gimme well_formed_formula. inversion. gimme lc. inversion.
apply : Lc.instantiate_pred. done. constructor.
nip. auto.
gimme fresh_in where atom. inversion.
rewrite <- instantiate_substitution_neq => //.
move => [n ?].
exists (S n). apply : (normal_intro_quant_fresh (a := b)) => //.

gimme Forall. rewrite ? Forall_forall. move => ? ?.
rewrite in_map_iff. move => [u [?]]. subst.
gimme where In. move //. by apply /fresh_in_substitute.
by apply : fresh_in_substitute.
}

{
cbn.
match goal with [_ : chain ?s ?a ?ts |- _] => rename a into b; rename s into s'; rename ts into params end.
gimme (chain). move /partial_chain_atom.
move /substitute_partial_chain. gimme lc. move => H'. move : (H'). move \\. move /(_ a).
move /eta_longness. move /(_ (map (substitute a s) Γ)).
nip. gimme Forall where well_formed_formula. rewrite ? Forall_forall. move => ?.
move => u. rewrite in_map_iff. move => [u' [?]]. subst.
gimme where well_formed_formula. move //.
inversion. constructor. by apply lc_substitute.
nip. apply in_map_iff. eexists. eauto.
nip. gimme Forall where normal_derivation. rewrite ? Forall_forall.
move => ? u. rewrite in_map_iff. move => [? [? ?]]. subst.
gimme (In). gimme where normal_derivation. move //. move /IH. nip. omega.
nip.
gimme (chain). move /partial_chain_atom. move /partial_chain_param_wff.
apply => //.
gimme Forall. rewrite Forall_forall. by apply.
nip.
all: done.
}
Qed.

Print Assumptions substitute_normal_derivation2.

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
have [a ?] := exists_fresh (u :: Γ).
decompose_Forall.
gimme where normal_derivation. move /(_ a).

gimme contains_depth; move /IH.
nip; first omega.
apply; try eassumption.

constructor.
apply : Lc.instantiate_pred => //.
gimme well_formed_formula where quant. inversion.
gimme lc. inversion. assumption.

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

(*
Lemma letstry : forall M Γ t, head_form M -> f_derivation Γ M t -> exists x s ts, In (x, s) Γ /\ partial_chain s t ts.
Proof.
move => M.
move : (term_depth <)
*)

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
intros. gimme normal_form. inversion.
gimme head_form. inversion. 
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