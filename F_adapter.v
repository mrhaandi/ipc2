Require Import List.
Require Import ListFacts.
Require Import Arith.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import Formula.
Require Import FormulaFacts.
From LCAC Require Import Relations_ext seq_ext_base ssrnat_ext seq_ext F.
Require Import UserTactics.
Require Import Derivations.
Require Import IIPC2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Wf_nat.
Require Import Psatz.

Ltac unfoldN := try arith_hypo_ssrnat2coqnat; do ?unfold addn, subn, muln, addn_rec, subn_rec, muln_rec, leq, Equality.sort, nat_eqType in *.

Ltac inspect_eqn := try (
  match goal with
  | [ |- context [eqn ?x ?y]] => 
    do [(have : x <> y by unfoldN; lia); move /eqP /negbTE; let H := fresh in move => H; cbn in H; move : H => -> |
     (have : x = y by unfoldN; lia); move /eqP; let H := fresh in move => H; cbn in H; move : H => ->]
  end).

Ltac inspect_eqn2 :=
  match goal with
  | [ |- context [?x == ?y]] => 
    do [(have : (x == y) = false by apply /eqP; unfoldN; lia); move => -> |
     (have : (x == y) = true by apply /eqP; unfoldN; lia); move => ->]
  | [ |- context [?x <= ?y]] => 
    do [(have : (x <= y) = false by apply /eqP; unfoldN; lia); move => -> |
     (have : (x <= y) = true by apply /eqP; unfoldN; lia); move => ->]
  end.

Inductive normal_form : term -> Prop :=
  | nf_hf : forall M, head_form M -> normal_form M
  | nf_abs : forall t M, normal_form M -> normal_form (abs t M)
  | nf_uabs : forall M, normal_form M -> normal_form (uabs M)
with head_form : term -> Prop :=
  | hf_var : forall n, head_form (var n)
  | hf_app : forall t1 t2, head_form t1 -> normal_form t2 -> head_form (app t1 t2)
  | hf_uapp : forall t1 ty, head_form t1 -> head_form (uapp t1 ty).

Fixpoint is_abs (t : term) : bool :=
  match t with
  | abs _ _ => true
  | _ => false
  end.


Fixpoint is_uabs (t : term) : bool :=
  match t with
  | uabs _ => true
  | _ => false
  end.


Fixpoint is_reducible (t : term) : bool :=
  match t with
  | var _ => false
  | app t1 t2 => is_abs t1 || is_reducible t1 || is_reducible t2
  | abs _ t1 => is_reducible t1
  | uapp t1 _ => is_uabs t1 || is_reducible t1
  | uabs t1 => is_reducible t1
  end.


Fixpoint term_size (t : term) : nat :=
  match t with
  | var _ => 1
  | app t1 t2 => 1 + term_size t1 + term_size t2
  | abs _ t1 => 1 + term_size t1
  | uapp t1 _ => 1 + term_size t1
  | uabs t1 => 1 + term_size t1
  end.


(*start induction on term size, usage: elim /term_size_ind.*)
Lemma term_size_ind : forall (P : term -> Prop) t, (forall (t1 : term), (forall (t2 : term), (term_size t2 < term_size t1)%coq_nat -> P t2) -> P t1) -> P t.
Proof.
move => P t H.
move Hn : (term_size t) => n.
move : n t Hn.
elim /lt_wf_ind => n IH.
move => t1 ?. subst.
eauto.
Qed.

(*if a term is reducible, construct some reductum*)
Lemma reduce_reducible : forall t, is_reducible t -> exists t', reduction1 t t'.
Proof.
elim /term_size_ind.

case; cbn.

discriminate.

move => t1 t2 IH. case /orP. case /orP.
clear. case : t1; cbn; try discriminate.
intros. eexists. constructor.

move /IH. move /(_ (ltac:(ssromega))). move => [t' ?].
eauto using reduction1.

move /IH. move /(_ (ltac:(ssromega))). move => [t' ?].
eauto using reduction1.

move => t1 t2 IH.
move /IH. move /(_ (ltac:(ssromega))). move => [t' ?].
eauto using reduction1.

move => t1 t2 IH. case /orP.
clear. case : t1; cbn; try discriminate.
intros. eexists. constructor.

move /IH. move /(_ (ltac:(ssromega))). move => [t' ?].
eauto using reduction1.

move => t1 IH.
move /IH. move /(_ (ltac:(ssromega))). move => [t' ?].
eauto using reduction1.
Qed.

(*find minimal element that is not further reducible*)
Lemma sn_to_not_reducible : forall t, SN t -> exists t', reduction t t' /\ (negb (is_reducible t')).
Proof.
move => t.
elim.
move => t2 H1 H2.
have := orbN (is_reducible t2).
case /orP.

{
move /reduce_reducible => [t3 Ht2].
move : (Ht2). move /H2 => [t' [? ?]].
exists t'. split => //=. apply : rt1n_trans; eassumption.
}

{
intro. exists t2. split; auto.
}
Qed.



(*a typable term that is not reducible is in normal form*)
Lemma not_reducible_to_nf : forall t (ty : typ) ctx, negb (is_reducible t) -> (Some ty == typing ctx t) -> normal_form t.
Proof.
elim /term_size_ind.
case.

(*var case*)
intros. do ? constructor.

(*app case*)
{
move => t1 t2 IH ty ctx.
rewrite /is_reducible -/is_reducible.
rewrite ? negb_or.
case /andP. case /andP. move => ? ? ?.
move /typing_appP.
case => tyl.
move => Ht1. move /IH. move /(_ (ltac:(cbn; ssromega)) (ltac:(done))) => ?.

move : (Ht1). move /IH. move /(_ (ltac:(cbn; ssromega)) (ltac:(done))).
inversion => //.

do 2 constructor => //.

move : Ht1. by case /typing_uabsP.
}

(*abs case*)
{
move => ty t IH ty2 t2.
rewrite /is_reducible -/is_reducible. move => ?.
case /typing_absP => tyr ?. subst.
move /IH. move /(_ (ltac:(cbn; ssromega)) (ltac:(done))).
eauto using normal_form.
}

(*uapp case*)
{
move => t ty IH ty2 ctx.
rewrite /is_reducible -/is_reducible.
rewrite ? negb_or.
case /andP. move => ? ?.
case /typing_uappP => ty3 ?. subst.
move => Ht. move : (Ht).
move /IH. move /(_ (ltac:(cbn; ssromega)) (ltac:(done))).
inversion => //.

eauto using normal_form, head_form.

move : Ht. by case /typing_absP.
}

(*uabs case*)
{
move => t IH ty t2.
rewrite /is_reducible -/is_reducible. move => ?.
case /typing_uabsP => tyr ?. subst.
move /IH. move /(_ (ltac:(cbn; ssromega)) (ltac:(done))).
eauto using normal_form.
}
Qed.

(*n is depth under uabs*)
Fixpoint formula_to_typ (labeling : label -> nat) (n : nat) (t : formula) : typ :=
  match t with
  | Formula.var x => tyvar x
  | atom a => tyvar (n + labeling a)
  | arr s t => tyfun (formula_to_typ labeling n s) (formula_to_typ labeling n t)
  | quant t => tyabs (formula_to_typ labeling (n.+1) t)
  end.

(*
(*atoms point to larger indices*)
Fixpoint typ_to_formula (n : nat) (t : typ) : formula :=
  match t with
  | tyvar x => if x > n then atom (0, x-n) else Formula.var x
  | tyfun s t => arr (typ_to_formula n s) (typ_to_formula n t)
  | tyabs t => quant (typ_to_formula (1+n) t)
  end.
 *)
(*Definition type_environment_to_basis (ctx : context typ) : list formula : (map (omap (typ_to_formula 0)) ctx).*)

(*
Lemma f_to_ipc : forall t (ty : typ) Gamma, 
 normal_form t -> (Some ty == typing (map (fun t => Some (formula_to_typ t)) Gamma) t) -> 
 exists n, normal_derivation n Gamma (typ_to_formula 0 ty).
*)

Lemma in_to_index : forall t Gamma, In t Gamma -> exists i, forall labeling n, ctxindex (map (fun t => Some (formula_to_typ labeling n t)) Gamma) i (formula_to_typ labeling n t).
Proof.
move => t. elim => //.
move => s Gamma IH.
case /in_cons_iff.

move => ?. subst. by exists 0.

move /IH => [n ?]. by exists (1+n).
Qed.


Lemma formula_to_typ_injective : forall labeling s t n, injective labeling -> lc n s -> lc n t -> formula_to_typ labeling n t = formula_to_typ labeling n s -> s = t.
Proof.
move => labeling s t n Hl.
elim : s t n => /=.

{
move => x. case => //=.
move => ? ? _ _. case => ?. f_equal. done.
move => ? ?. inversion. inversion. case => ?. unfoldN. lia.
}

{
move => a. case => //=.
move => ? ?. inversion. inversion. case => ?. unfoldN. lia.
move => b ? _ _. case => ?.
have : labeling a = labeling b by unfoldN; lia.
move /Hl => ?. f_equal. done.
}

{
move => s1 IHs1 s2 IHs2. case => //=.
intros *. inversion. inversion. inversion. f_equal; eauto.
}

{
move => s IH. case => //=.
intros *. inversion. inversion. inversion. f_equal. eauto.
}
Qed.


Lemma index_to_in : forall t Gamma i labeling n, injective labeling -> Forall (lc n) Gamma -> lc n t -> ctxindex (map (fun t => Some (formula_to_typ labeling n t)) Gamma) i (formula_to_typ labeling n t) -> In t Gamma.
Proof.
move => t. elim => //=.
case => //=.

move => s Gamma IH.
case => //=.

intros * => ?. case => ? ? ?. move /eqP. case.
move /formula_to_typ_injective. auto.

intros * => ?. case => ? ? ?.
move /IH. auto.
Qed.

(*
Lemma instantiate_subst_eq : forall t s n, formula_to_typ n (instantiate t n s) = subst_typ n [:: formula_to_typ n t] (formula_to_typ n s).
Proof.
(*
move => t.
elim; cbn.

{
move => m n.
have : n = m \/ lt n m \/ lt m n by lia. case; last case.

move => ?. subst.

have : (m - m)%Nrec = 0 by ssromega.
move => ->.
cbn.
inspect_eqb.

admit. admit. admit.
}

admit.

all: intros; by f_equal.
*)
Admitted.
*)

Lemma exists_labeling : exists (labeling : label -> nat), injective labeling. Admitted.

(*increases all free type variables by 1 except a which is set to zero*)
Fixpoint shift_typ_0 (a : nat) c t :=
  match t with
    | tyvar n => tyvar (if c+a == n then c else (if c <= n then n.+1 else n))
    | tl ->t tr => shift_typ_0 a c tl ->t shift_typ_0 a c tr
    | tyabs t => tyabs (shift_typ_0 a (c.+1) t)
  end.

(*
Lemma shift_typ_0_shift : forall a ty n m, m <= n -> shift_typ 1 m (shift_typ_0 a n ty) = shift_typ_0 a n.+1 (shift_typ 1 m ty).
Proof.
Admitted.
*)

Lemma shift_typ_0_shift : forall a m ty n d, d <= n ->
  shift_typ_0 a (m + n) (shift_typ m d ty) = shift_typ m d (shift_typ_0 a n ty).
Proof.
move => a m. elim => /=.
move => n' n d ?.
have : (d <= n')%coq_nat \/ (d > n')%coq_nat by lia.
case => ?; do ? inspect_eqn2 => //.
have : (n + a = n')%coq_nat \/ (n + a <> n')%coq_nat by lia.
case => ?; do ? inspect_eqn2; try (f_equal; unfoldN; lia).
have : (n <= n')%coq_nat \/ (n > n')%coq_nat by lia.
case => ?; do ? inspect_eqn2 => //.

intros; f_equal; auto.

move => ? IH *. f_equal.
have : forall n m, (n + m).+1 = (n + m.+1) by intros; unfoldN; lia. move => ->.
auto.
Qed.

Fixpoint subst_typ_1 n s t := 
  match t with
    | tyvar m => if n == m then (shift_typ n 0 s) else if n < m then tyvar (m-1) else tyvar m
    | tl ->t tr => subst_typ_1 n s tl ->t subst_typ_1 n s tr
    | tyabs t => tyabs (subst_typ_1 n.+1 s t)
  end.



(*
Lemma labeling_ext : forall t labeling1 labeling2, (forall a, labeling1 a = labeling2 a) -> formula_to_typ labeling1 t = formula_to_typ labeling2 t.
Proof.
elim; cbn; intros; f_equal; eauto.
Qed.
*)

Lemma subst_typ_to_subst_typ_1 : forall s t n, subst_typ n [:: s] t = subst_typ_1 n s t.
Proof.
move => s. elim => /=.
move => n m.
have : (m = n) \/ (lt m n) \/ (lt n m) by lia.
(case; last case) => ?.

subst. do ? inspect_eqn2.
have : (n - n) = 0 by unfoldN; lia. by move => ->.

do ? inspect_eqn2. move => /=.

have : (n - m) = (n - m - 1).+1 by ssromega. move => -> /=.
move : {2}(n - m - 1) => d. case : d; cbn; unfoldN; intros; f_equal; lia.

by do ? inspect_eqn2.

all: intros; f_equal; eauto.
Qed.


Lemma shift_typ_0_subst : forall a d tyr tyl m,
  shift_typ_0 a (m+d) (subst_typ_1 m tyr tyl) = subst_typ_1 m (shift_typ_0 a d tyr) (shift_typ_0 a (m+d).+1 tyl).
Proof.
move => a d tyr. elim => /=.

move => n' m.
have : (m = n') \/ (m < n')%coq_nat \/ (m > n')%coq_nat by lia.
(case; last case) => ?; do ? inspect_eqn2.
subst. apply : shift_typ_0_shift. ssromega.

have : ((d + m).+1 + a = n') \/ ((d + m).+1 + a <> n') by lia.
case => ?; do ? inspect_eqn2.
subst => /=. f_equal. do ? inspect_eqn2. unfoldN. lia.
have : (d + m < n')%coq_nat \/ (d + m >= n')%coq_nat by lia.
case => ?; do ? inspect_eqn2.
1-3: move => /=; do ? inspect_eqn2; f_equal; unfoldN; lia.


intros. f_equal; auto.
intros. f_equal.
have : forall d m, (m + d).+1 = (m.+1 + d) by intros; unfoldN; lia. move => ->. auto.
Qed.

Lemma shift_typ_0_preserves_typing a n ctx t ty : 
  ctx \|- t \: ty ->
  ctxmap (shift_typ_0 a n) ctx \|-
    typemap (shift_typ_0 a) n t \: shift_typ_0 a n ty.
Proof.
elim: t ty n ctx =>
  [m | tl IHtl tr IHtr | tyl t IHt | t IHt tyr | t IHt] ty n ctx /=.
- by apply ctxindex_map.
- by case/typing_appP => tyl H H0; apply/typing_appP;
    exists (shift_typ_0 a n tyl); [apply (IHtl (tyl ->t ty)) | apply IHtr].
- by case/typing_absP => tyr -> H; rewrite /= typing_absE; move: H; apply IHt.
- case/typing_uappP => tyl -> H; apply/typing_uappP.
    exists (shift_typ_0 a (n.+1) tyl).
rewrite ? subst_typ_to_subst_typ_1.
  + by apply : shift_typ_0_subst.
  + by move: H; apply IHt.
- case/typing_uabsP => ty' -> H; rewrite /= typing_uabsE.
  move : H. move /IHt. move /(_ n.+1).
  apply : eq_ind.

  do 2 f_equal.
  clear; rewrite -!map_comp; apply eq_map; case => //= ty''; f_equal. symmetry. apply : shift_typ_0_shift. done.
Qed.


Lemma labeling_shift_typ_eq : forall labeling m t n, lc n t -> formula_to_typ labeling (n+m) t = shift_typ m n (formula_to_typ labeling n t).
Proof.
move => labeling m. elim; cbn; intros; grab lc; inversion; f_equal; auto.

by inspect_eqn.
inspect_eqn. unfoldN. lia.
grab lc. grab where formula_to_typ. move => IH /IH. auto.
Qed.

Lemma instantiate_subst_typ_eq : forall labeling s n t, lc 0 t -> lc (n.+1) s -> 
  formula_to_typ labeling n (instantiate t n s) = subst_typ_1 n (formula_to_typ labeling 0 t) (formula_to_typ labeling (n.+1) s).
Proof.
move => labeling s n t Ht.
elim : s n.

move => m n. inversion. cbn.
have : (m = n) \/ (m < n)%coq_nat by lia. case.
move => ?. subst.
inspect_eqb. inspect_eqn.
by apply : (@labeling_shift_typ_eq _ _ _ 0).

move => ?.
inspect_eqb. inspect_eqn. cbn.
revert dependent m. case; cbn => //.
intros. by inspect_eqn.

cbn. move => a n _.
do ? inspect_eqn.
unfoldN. f_equal. lia.

cbn. intros. grab lc. inversion. f_equal; eauto.

cbn. move => s IH n. inversion. f_equal. eauto.
Qed.


Lemma bind_shift_eq : forall a t labeling n, injective labeling -> lc n t ->
  formula_to_typ labeling (n.+1) (bind a n t) = shift_typ_0 (labeling a) n (formula_to_typ labeling n t).
Proof.
move => a. elim; cbn.
move => m labeling n _. inversion.
by do ? inspect_eqn.

move => b labeling n Il _.
case : (Label.eq_dec a b).
move => H. move : (H) => /Label.eqb_eq ->.
subst. inspect_eqn. done.

move => H. move : (H) => /Label.neq_neqb ->.
have ? : labeling a <> labeling b by auto.
do ? inspect_eqn. done.

by intros; grab lc; inversion; f_equal; auto.

move => t IH labeling n *. f_equal. grab lc. inversion.
apply : IH; cbn => //.
Qed.


Lemma shift_typ_0_fresh : forall a t labeling n, injective labeling -> fresh_in a t -> lc n t -> 
  shift_typ 1 n (formula_to_typ labeling n t) = shift_typ_0 (labeling a) n (formula_to_typ labeling n t).
Proof.
move => a. elim.
move => m labeling n _ _. inversion.
cbn. by do ? inspect_eqn.

move => b labeling n ?. inversion. move => _.
cbn. have ? : labeling a <> labeling b by auto. do ? inspect_eqn. f_equal. unfoldN. lia.

cbn; intros; grab lc; inversion; grab fresh_in; inversion; f_equal; auto.

cbn. move => t IH labeling n *.
grab lc; inversion; grab fresh_in; inversion.
f_equal.
apply : IH => //.
Qed.

(*if there is an iipc2 derivation, then there is a corresponding system F typing*)
Lemma iipc2_to_f : forall Gamma t, iipc2 Gamma t -> forall labeling, injective labeling -> exists M, (Some (formula_to_typ labeling 0 t) == typing (map (fun t => Some (formula_to_typ labeling 0 t)) Gamma) M).
Proof.
move => Gamma t.
elim; clear => Gamma.

(*var case*)
{
move => t ?.
move /in_to_index => [n ?].
move => labeling ?.
exists (var n). eauto.
}

(*app case*)
{
move => s t _ HM _ HN ? ?.
move : (HM _ ltac:(eassumption)) => [M ?].
move : (HN _ ltac:(eassumption)) => [N ?].
exists (app M N). apply /typing_appP. eexists; eauto.
}

(*abs case*)
{
move => s t _ HM labeling ?.
move : (HM _ ltac:(eassumption)) => [M ?].
exists (abs (formula_to_typ labeling 0 s) M).
apply /typing_absP. by eexists.
}

(*uapp case*)
{
move => s t ? /iipc2_wff. case => ?. inversion. move => HM labeling ?.
move : (HM _ ltac:(eassumption)) => [M ?].
exists (uapp M (formula_to_typ labeling 0 t)).
apply /typing_uappP.
eexists; try eassumption.
rewrite -/formula_to_typ. rewrite subst_typ_to_subst_typ_1.

apply instantiate_subst_typ_eq => //.
}

(*uabs case*)
{
move => t a ? ? HM labeling ?.
move : HM. move /(_ _ ltac:(eassumption)) => [M].
move /(@shift_typ_0_preserves_typing (labeling a) 0).
move => HM.

exists (uabs (typemap (shift_typ_0 (labeling a)) 0 M)). (*also need rename labeling a to 0*)
apply /typing_uabsP.
eexists. cbn. reflexivity.
move : HM. apply : eq_ind.
rewrite -!map_comp.
grab iipc2. move /iipc2_wff => [? ?].

do 2 f_equal.
apply bind_shift_eq => //.

grab List.Forall. grab List.Forall. grab injective. clear => ?.
elim : Gamma => //.

move => t Gamma IH. inversion. inversion.
cbn. f_equal; last auto.
f_equal.
apply shift_typ_0_fresh => //.
}
Qed.

Print Assumptions iipc2_to_f.

(*chain s a params morally means that s can be instanciated as p1 -> ... -> pn -> a*)
Inductive partial_chain (s t : formula) : list formula -> Prop :=
  | partial_chain_nil : contains s t -> partial_chain s t List.nil
  | partial_chain_cons : forall (s' t': formula) (ts: list formula), contains s (arr s' t') -> partial_chain t' t ts -> partial_chain s t (s' :: ts).


Lemma typ_to_formula : forall ty labeling n, bijective labeling -> exists t, ty = (formula_to_typ labeling n t) /\ lc n t.
Proof.
elim => /=.
move => x labeling n. case => l_inv. rewrite /cancel => _ Hl_inv.
have : (x < n)%coq_nat \/ (x >= n)%coq_nat by lia.
case => ?.
exists (Formula.var x). split; by constructor.
exists (Formula.atom (l_inv (x-n))) => /=. split; last constructor. f_equal. rewrite Hl_inv. unfoldN. lia.

move => tyl IHs tyr IHt *.
move : (IHs ltac:(assumption) ltac:(assumption) ltac:(assumption)) => [s [-> ?]].
move : (IHt ltac:(assumption) ltac:(assumption) ltac:(assumption)) => [t [-> ?]].
exists (Formula.arr s t). split; by constructor.

move => ty IH ? n *.
move : (IH ltac:(assumption) (n.+1) ltac:(assumption)) => [t [-> ?]].
exists (Formula.quant t). split; by constructor.
Qed.


Lemma partial_chain_arr : forall ts s t u, partial_chain s (arr t u) ts -> partial_chain s u (ts ++ [::t]).
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

Lemma contains_transitivity : forall s t u, contains s t -> contains t u -> contains s u.
Proof.
intros until 0; elim => //.
intros; apply : contains_trans; eauto.
Qed.

Lemma partial_chain_contains : forall s t t' ts, partial_chain s t ts -> contains t t' -> partial_chain s t' ts.
Proof.
intros *.
elim => *.
constructor. apply : contains_transitivity; eauto.
apply : partial_chain_cons; eauto.
Qed.

Lemma shift_formula_to_typ labeling : forall t n m, lc m t -> shift_typ n m (formula_to_typ labeling m t) = formula_to_typ labeling (m+n) t.
Proof.
elim => /=.
intros *. inversion. by inspect_eqn2.
intros * => _. inspect_eqn2. f_equal. unfoldN. lia.
intros. grab lc. inversion. f_equal; auto.
intros. grab lc. inversion. f_equal.
have : (m + n).+1 = (m.+1 + n) by unfoldN; lia. move => ->. auto.
Qed.

(*
Lemma formula_to_typ_instantiate : forall u ty labeling, injective labeling -> ty = formula_to_typ labeling 0 u -> forall s n t, lc (n.+1) s -> lc n t ->
  formula_to_typ labeling n t = subst_typ_1 n ty (formula_to_typ labeling (n.+1) s) ->
  instantiate u n s = t.
Proof.
move => u ty labeling Hl ?. elim => /=.

move => x n t. inversion. move => ?.
have : (x = n) \/ (x < n)%coq_nat by lia.
case => ?.
subst. inspect_eqn2. inspect_eqb.
rewrite shift_formula_to_typ. cbn.
apply /formula_to_typ_injective => //.
admit. admit. (*doable? - maybe NOT*)
do ? inspect_eqn2. inspect_eqb.
revert dependent t. case => //=.
move => ? ?. case. intros. by subst.
move => ? ?. case. intros. unfoldN. lia.

move => a n t _ ?. do ? inspect_eqn2.
revert dependent t. case => //=.
move => ?. inversion. case => ?. unfoldN. lia.
move => b _. case => ?. f_equal. apply : Hl. unfoldN. lia.

move => s1 IHs1 s2 IHs2 n t. inversion.
case : t => //= => t1 t2. inversion.
case => ? ?. f_equal; eauto.

move => s IHs n t. inversion.
case : t => //= => t. inversion.
case => ?. f_equal; eauto.
Admitted.
*)



(*NEXT: if there is a derivation, then there is a ipc2 long derivation*)
Lemma f_hf_to_partial_chain : forall labeling, bijective labeling -> forall M Gamma t, 
  Forall well_formed_formula Gamma -> well_formed_formula t -> head_form M -> (Some (formula_to_typ labeling 0 t) == typing (map (fun t => Some (formula_to_typ labeling 0 t)) Gamma) M) ->
  exists s ts, In s Gamma /\ partial_chain s t ts /\ 
    (List.Forall (fun t' => exists M', normal_form M' /\ term_size M' < term_size M /\ (Some (formula_to_typ labeling 0 t') == typing (map (fun t => Some (formula_to_typ labeling 0 t)) Gamma) M')) ts).
Proof.
move => labeling Hl.
elim /term_size_ind.
move => M IH Gamma t ? ?. inversion.

(*var case*)
{
rewrite typing_varE. move /index_to_in.
move /(_ ltac:(auto using bij_inj) ltac:(assumption) ltac:(assumption)) => ?.
eexists. exists [::]. split; first eassumption.
split; do ? constructor.
}

(*app case*)
{
move /typing_appP => [tyl].
have [s [-> ?]] := (@typ_to_formula tyl labeling 0 ltac:(assumption)).
move /(@IH _ _ _ (Formula.arr s t)) => /=.
move /(_ ltac:(unfoldN; lia) ltac:(assumption) ltac:(by constructor) ltac:(assumption)).
move => [s' [ts' [? [? ?]]]] ?.
exists s', (ts' ++ [::s]). split; first done.
split. by apply : partial_chain_arr.
rewrite Forall_app_iff. split.
grab List.Forall. apply : List.Forall_impl.
clear => t [M [? [? ?]]].
exists M. split; first done.
split; last done. apply /leP. unfoldN. lia.

constructor; last done.
eexists. split; first eassumption. 
split; last done. apply /leP. unfoldN. lia.
}

(*TODO uapp case*)
{
move /typing_uappP => [tyl]. rewrite subst_typ_to_subst_typ_1.
have [s' [-> ?]] := (@typ_to_formula tyl labeling 1 ltac:(assumption)).
move => ?.
move /(@IH _ _ _ (Formula.quant s')) => /=.
move /(_ ltac:(unfoldN; lia) ltac:(assumption) ltac:(by constructor) ltac:(assumption)).
move => [s'' [ts'' [? [? ?]]]].
exists s'', ts''. split; first done.
split.
apply : partial_chain_contains; eauto.
have [s [? ?]]:= typ_to_formula ty 0 ltac:(eassumption). subst.
grab where subst_typ_1. rewrite <- instantiate_subst_typ_eq => //.
move /formula_to_typ_injective. move /(_ ltac:(auto using bij_inj) ltac:(auto using Lc.instantiate_pred) ltac:(assumption)).
move => <-. apply : contains_trans; first last; [constructor | done].
grab List.Forall. apply : List.Forall_impl.
clear => t [M [? [? ?]]].
exists M. split; first done.
split; last done. apply /leP. unfoldN. lia.
}
Qed.

(*NEXT: if there is a derivation, then there is a ipc2 long derivation*)
Lemma f_to_normal_derivation : forall Gamma t M labeling, injective labeling -> 
  (Some (formula_to_typ labeling 0 t) == typing (map (fun t => Some (formula_to_typ labeling 0 t)) Gamma) M) ->
  exists d, normal_derivation d Gamma t.
Proof.

