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

Ltac unfoldN := do ? arith_hypo_ssrnat2coqnat; do ?unfold addn, subn, muln, addn_rec, subn_rec, muln_rec, leq, Equality.sort, nat_eqType in *.

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

Fixpoint typ_size (t : typ) : nat :=
  match t with
  | tyvar _ => 1
  | tyfun t1 t2 => 1 + typ_size t1 + typ_size t2
  | tyabs t1 => 1 + typ_size t1
  end.



Fixpoint formula_size (t : formula) : nat :=
  match t with
  | Formula.var _ => 1
  | Formula.atom _ => 1
  | Formula.arr t1 t2 => 1 + formula_size t1 + formula_size t2
  | Formula.quant t1 => 1 + formula_size t1
  end.


(*start induction on measure, usage: elim /(@f_ind term term_size).*)
Lemma f_ind (A : Type) (f : A -> nat) : forall  (P : A -> Prop) t, (forall (t1 : A), (forall (t2 : A), (f t2 < f t1)%coq_nat -> P t2) -> P t1) -> P t.
Proof.
move => P t H.
move Hn : (f t) => n.
move : n t Hn.
elim /lt_wf_ind => n IH.
move => t1 ?. subst.
eauto.
Qed.

Arguments f_ind [A].

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


Lemma nf_cases : forall M, (head_form M \/ (~(head_form M) /\ normal_form M) \/ ~(normal_form M)).
Proof with auto using head_form, normal_form.
elim.
move => n. left. auto using head_form, normal_form.
move => M. (case; last case) => ? N; try (grab and; case => ? ?); (case; last case) => ?; try (grab and; case => ? ?).
1-2: idtac...
1-7: right; right; inversion; grab head_form; inversion...

move => ty M. (case; last case) => ?; try (grab and; case => ? ?).
right; left; split; [inversion | apply nf_abs; by constructor ].
right; left; split; [inversion | by apply nf_abs ].
right; right; inversion; [grab head_form; inversion | done].

move => M. (case; last case) => ?; try (grab and; case => ? ?); move => ty.
idtac...
1-2: right; right; inversion; grab head_form; inversion...

move => M. (case; last case) => ?; try (grab and; case => ? ?).
right; left; split; [inversion | apply nf_uabs; by constructor ].
right; left; split; [inversion | by apply nf_uabs ].
right; right; inversion; [grab head_form; inversion | done].
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

Fixpoint is_head_form (M : term) : bool :=
  match M with
  | var _ => true
  | app M _ | uapp M _ => is_head_form M
  | _ => false
  end.

Fixpoint eta_weight (ty : typ) : nat :=
  match ty with
  | tyvar _ => 0
  | tyfun tyl tyr => 1 + eta_weight tyr
  | tyabs ty => 1 + eta_weight ty
  end.

(*w is maximal weight and h is true iff inside head for inspection*)
Fixpoint is_eta_long (ctx : context typ) (M : term) (w : nat) (h : bool) : bool :=
  match M with
  | var x => if (typing ctx M) is Some ty then h || (typ_size ty <= w.+1) else false
  | app M' N' => if (typing ctx M) is Some ty then (h || (typ_size ty <= w.+1)) && is_eta_long ctx M' w true && is_eta_long ctx N' w false else false
  | uapp M' _ => if (typing ctx M) is Some ty then (h || (typ_size ty <= w.+1)) && is_eta_long ctx M' w true else false
  | abs tyl M' => is_eta_long ((Some tyl)::ctx) M' w false
  | uabs M' => is_eta_long (ctxmap (shift_typ 1 0) ctx) M' w false
  end.

(*h is true when outermost type matters for head form*)
Fixpoint eta_deficiency (ctx : context typ) (M : term) (h : bool) : nat :=
  if (typing ctx M) is Some ty then
    match M with
    | var x => if h then (typ_size ty) - 1 else 0
    | app M N => eta_deficiency ctx M false + eta_deficiency ctx N true + if h then (typ_size ty) - 1 else 0
    | uapp M _ => eta_deficiency ctx M false + if h then (typ_size ty) - 1 else 0
    | abs tyl M => eta_deficiency (Some tyl :: ctx) M true
    | uabs M => eta_deficiency (ctxmap (shift_typ 1 0) ctx) M true
    end
  else 0.


Lemma shift_typing : forall ctx ty M, typing (Some ty :: ctx) (shift_term 1 0 M) = typing ctx M.
Proof.
intros.
have := @subject_reduction_proof.typing_shift M 0 ctx [:: Some ty].
cbn => <-. f_equal. clear. rewrite /insert. cbn.
case: ctx; reflexivity.
Qed.

(*pulls out typing expressions out of match*)
Ltac exists_matching_typing := 
  match goal with [|- context[match typing ?ctx ?M with | Some _ => _ | None => _ end]] => 
    let ty := fresh "ty" in evar (ty : typ); let ty' := eval red in ty in 
      (have : Some ty' == typing ctx M); last (move => /eqP <-); try eassumption end.


Lemma subt_typ_id : forall ty (n : nat), subst_typ_1 n (tyvar 0) (shift_typ 1 (n.+1) ty) = ty.
Proof.
elim => /=.
move => x n.
have : (n < x)%coq_nat \/ (n = x)%coq_nat \/ (n > x)%coq_nat by lia.
(case; last case) => ?; do ? inspect_eqn2; f_equal; unfoldN; lia.
move => tyl IHl tyr IHr n. by rewrite (IHl n) (IHr n).
move => ty IH n. by rewrite (IH n.+1).
Qed.


Lemma shift_forms : forall M n, 
  (head_form M -> head_form (shift_term 1 n M)) /\ (normal_form M -> normal_form (shift_term 1 n M)).
Proof.
elim => /=.
move => x n. case : (n <= x); split; auto using normal_form, head_form.

move => M IHM N IHN n.
split.
inversion. constructor; firstorder done.
inversion. grab head_form. inversion. constructor; constructor; firstorder done.

move => ty M IH n.
split. inversion.
inversion. grab head_form. inversion.
apply nf_abs. firstorder done.

intros.
split. inversion. constructor; firstorder done.
inversion. grab head_form. inversion. constructor; constructor; firstorder done.

intros.
split. inversion.
inversion. grab head_form. inversion.
apply : nf_uabs. firstorder done.
Qed.

Lemma shift_head_form : forall M n, head_form M -> head_form (shift_term 1 n M). 
Proof. 
firstorder done using shift_forms.
Qed.

Lemma shift_normal_form : forall M n, normal_form M -> normal_form (shift_term 1 n M). 
Proof. 
firstorder done using shift_forms.
Qed.


Lemma map_forms : forall M n, 
  (head_form M -> head_form (typemap (shift_typ 1) n M)) /\ (normal_form M -> normal_form (typemap (shift_typ 1) n M)).
Proof.
elim => /=.
move => x n. case : (n <= x); split; auto using normal_form, head_form.

move => M IHM N IHN n.
split.
inversion. constructor; firstorder done.
inversion. grab head_form. inversion. constructor; constructor; firstorder done.

move => ty M IH n.
split. inversion.
inversion. grab head_form. inversion.
apply nf_abs. firstorder done.

intros.
split. inversion. constructor; firstorder done.
inversion. grab head_form. inversion. constructor; constructor; firstorder done.

intros.
split. inversion.
inversion. grab head_form. inversion.
apply : nf_uabs. firstorder done.
Qed.

Lemma map_head_form : forall M n, head_form M -> head_form (typemap (shift_typ 1) n M). 
Proof. 
firstorder done using map_forms.
Qed.

Lemma map_normal_form : forall M n, normal_form M -> normal_form (typemap (shift_typ 1) n M). 
Proof. 
firstorder done using map_forms.
Qed.


Lemma eta_shift_term : forall M ty ctx n h, eta_deficiency (ctxinsert [:: Some ty] ctx n) (shift_term 1 n M) h = eta_deficiency ctx M h.
Proof.
elim /(f_ind term_size).

case => /=.

move => x IH ? ? n ?.
(have : var (if n <= x then x + 1 else x) = shift_term 1 n (var x) by reflexivity) => ->.
rewrite subject_reduction_proof.typing_shift.
done.

move => M N IH ? ? n ?.
(have : (shift_term 1 n M @ shift_term 1 n N) = shift_term 1 n (M @ N) by reflexivity) => ->.
rewrite subject_reduction_proof.typing_shift.
move : (IH M ltac:(ssromega)). move => ->.
move : (IH N ltac:(ssromega)). move => ->.
done.

move => tyl M IH ty ctx n ?.
(have : (abs tyl (shift_term 1 n.+1 M)) = shift_term 1 n (abs tyl M) by reflexivity) => ->.
rewrite subject_reduction_proof.typing_shift.
(have : (Some tyl :: ctxinsert [:: Some ty] ctx n) = ctxinsert [:: Some ty] (Some tyl :: ctx) n.+1 by reflexivity) => ->.
move : (IH M ltac:(ssromega)). move => ->.
done.

move => M tyl IH ? ? n ?.
(have : (shift_term 1 n M @' tyl) = shift_term 1 n (M @' tyl) by reflexivity) => ->.
rewrite subject_reduction_proof.typing_shift.
move : (IH M ltac:(ssromega)). move => ->.
done.

move => M IH ty ctx n ?.
(have : (uabs (shift_term 1 n M)) = shift_term 1 n (uabs M) by reflexivity) => ->.
rewrite subject_reduction_proof.typing_shift.
have : ctxmap (shift_typ 1 0) (ctxinsert [:: Some ty] ctx n) = ctxinsert [:: Some (shift_typ 1 0 ty)] (ctxmap (shift_typ 1 0) ctx) n.
clear.
move : (shift_typ 1 0) => f.
elim : ctx n.
elim => //=.
move => n IH. cbn. f_equal. move : IH. cbn.
have : (n - 0)%Nrec = n by unfoldN; lia. move => ->.
move => <-.
f_equal.

move => /= a ctx IH.
elim => //= n IHn.
have : ctxinsert [:: Some (f ty)] (omap f a :: ctxmap f ctx) n.+1 = omap f a :: (ctxinsert [:: Some (f ty)] (ctxmap f ctx) n) by reflexivity. 
move => ->.
f_equal. by rewrite <- IH.

move => ->.
by move : (IH M ltac:(ssromega)) => ->.
Qed.


Lemma shift_typ_size : forall ty n, typ_size (shift_typ 1 n ty) = typ_size ty.
Proof.
elim => //=; intros; auto.
Qed.


Lemma eta_shift_typ :forall M ctx n h, 
  eta_deficiency (ctxmap (shift_typ 1 n) ctx) (typemap (shift_typ 1) n M) h = eta_deficiency ctx M h.
Proof.
have typing_shifttyp : forall t M d c ctx, M = (typemap (shift_typ d) c t) -> typing (ctxmap (shift_typ d c) ctx) M = omap (shift_typ d c) (typing ctx t) by
intros; subst; apply subject_reduction_proof.typing_shifttyp.

elim => /=.

move => x ctx n h.
rewrite -> (typing_shifttyp (var x)); last done.
case : (typing ctx x) => //=.
intros. by rewrite shift_typ_size.

move => M IHM N IHN ctx n h.
rewrite -> (typing_shifttyp (M @ N)); last done.
case : (typing ctx (M @ N)) => //= ?.
rewrite IHM IHN. by rewrite shift_typ_size.

move => ty M IH ctx n h.
rewrite -> (typing_shifttyp (abs ty M)); last done.
case : (typing ctx (abs ty M)) => //= ?.
have : (Some (shift_typ 1 n ty) :: ctxmap (shift_typ 1 n) ctx) = ctxmap (shift_typ 1 n) (Some ty :: ctx) by reflexivity.
move => ->. rewrite IH. done.

move => M IH ty ctx n h.
rewrite -> (typing_shifttyp (M @' ty)); last done.
case : (typing ctx (M @' ty)) => //= ?.
rewrite IH. by rewrite shift_typ_size.

move => M IH ctx n h.
rewrite -> (typing_shifttyp (uabs M)); last done.
case : (typing ctx (uabs M)) => //= ?.
rewrite <- (@IH (ctxmap (shift_typ 1 0) ctx) n.+1).
f_equal.
clear. elim : ctx => //=.
case => [a |]; move => ctx ? /=; f_equal; auto.
f_equal. rewrite -> shift_shift_distr_ty.
f_equal. done.
Qed.


Lemma ctx_prepend : forall ctx (ty : typ), ctxinsert [:: Some ty] ctx 0 = (Some ty) :: ctx.
Proof.
move => ctx ty. rewrite /insert.
have : (0 - size ctx) = 0 by unfoldN; lia. move => ->.
by case : ctx.
Qed.


Lemma typ_size_pos : forall ty, 0 < typ_size ty.
Proof.
elim => /=; intros; apply /leP; unfoldN; lia.
Qed.


Lemma eta_expand : forall (M : term) (ctx : context typ) (ty : typ) (w : nat), Some ty == typing ctx M -> 
  (normal_form M -> eta_deficiency ctx M true <= w.+1 ->
  exists N, normal_form N /\ (Some ty == typing ctx N) /\ eta_deficiency ctx N true <= w) /\
  (head_form M -> eta_deficiency ctx M false <= w.+1 ->
  exists N, head_form N /\ (Some ty == typing ctx N) /\ eta_deficiency ctx N false <= w).
Proof.
elim /(f_ind term_size). case.

(*var case*)
{
move => x IH ctx ty w Hty.
split => _.
admit. (*case analysis on ty*)
move => _. exists (var x). 
split. by auto using normal_form, head_form.
split. done.
rewrite /eta_deficiency. move : Hty => /eqP <-. apply /leP. lia.
}

(*app case*)
{
move => M N IH ctx ty w Hty => /=; move : (Hty) => /eqP <-.
move : (Hty). move /typing_appP => [tyl] HM HN.
split.
(*nf app case*)
{
inversion. grab head_form. inversion. move.
revert dependent ty. case.
(*target is tyvar case*)
admit.
(*target is tyfun case*)
{
move => tyl' ty Hty HM.
pose L := (abs tyl' (shift_term 1 0 (M @ N) @ 0)).
have HL : Some (tyfun tyl' ty) == typing ctx L.
apply /typing_absP. eexists. reflexivity. apply /typing_appP.
eexists. rewrite shift_typing. eassumption. done.

move => /= ?. exists L.
split. apply nf_abs. apply nf_hf. apply hf_app; [apply : shift_head_form | ]; auto using head_form, normal_form.
split. done.
move => /=. 
exists_matching_typing.
exists_matching_typing. move : HL. rewrite typing_absE => ?. eassumption.
exists_matching_typing. move : Hty. rewrite <- (@shift_typing _ tyl') => ?. eassumption.
rewrite <- ctx_prepend. rewrite ? eta_shift_term.
apply /leP.
have ? := typ_size_pos tyl'. have ? := typ_size_pos ty.
unfoldN. lia.
}
(*target is tyabs*)
{
move => ty Hty HM.
pose L := (uabs ((typemap (shift_typ 1) 0 (M @ N)) @' 0)).
have HL : Some (tyabs ty) == typing ctx L.
apply /typing_uabsP. eexists. reflexivity. apply /typing_uappP.
eexists; first last. rewrite subject_reduction_proof.typing_shifttyp.
move : Hty => /eqP <-. apply /eqP. cbn. reflexivity.
rewrite subst_typ_to_subst_typ_1. by rewrite subt_typ_id.
move => /= ?.

exists L.
split. apply nf_uabs. apply nf_hf. apply hf_uapp.
apply map_head_form. auto using head_form.

split. done.
move => /=.
exists_matching_typing.
exists_matching_typing. move : HL. rewrite typing_uabsE => ?. eassumption.
exists_matching_typing. 
have : typemap (shift_typ 1) 0 M @ typemap (shift_typ 1) 0 N = typemap (shift_typ 1) 0 (M @ N) by reflexivity. move => ->.
rewrite subject_reduction_proof.typing_shifttyp. move : Hty => /eqP <-. cbn. apply /eqP. reflexivity.
rewrite -> ? eta_shift_typ.
have ? := typ_size_pos ty. apply /leP. unfoldN. lia.
}
}
(*hf app case*)
{
inversion => ?.
move : (HM) => /IH. move /(_ ltac:(cbn; unfoldN; lia) (eta_deficiency ctx M false - 1)).
case => _. move /(_ ltac:(assumption) ltac:(apply /leP; unfoldN; lia)) => [M' [? [? ?]]].
move : (HN) => /IH. move /(_ ltac:(cbn; unfoldN; lia) (eta_deficiency ctx N true - 1)).
case. move /(_ ltac:(assumption) ltac:(apply /leP; unfoldN; lia)) => [N' [? [? ?]]].
move => _. exists (app M' N').
split. by auto using head_form.
split. apply /typing_appP. by eauto.
move => /=.
exists_matching_typing. apply /typing_appP. eexists; eassumption.
apply /leP. unfoldN. lia.
}
}
(*abs case*)
{
move => tyl M IH ctx ty w. move /typing_absP => [tyr -> HM].
split; inversion. grab head_form. by inversion. move => ?.
move : (HM). move /IH. move /(_ ltac:(ssromega) w). case.
move /(_ ltac:(assumption)).
apply : unnest.
grab where eta_deficiency. move => /=.
exists_matching_typing. apply /typing_absP. eexists. reflexivity. eassumption. done.
move => [N [? [? ?]]] _.
exists (abs tyl N).
split. by auto using normal_form.
split. apply /typing_absP. eexists. reflexivity. assumption.
move => /=.
exists_matching_typing. apply /typing_absP. eexists. reflexivity. eassumption.
}
(*uapp case*)
{
admit.
}
(*uabs case*)
{
move => M IH ctx ty w. move /typing_uabsP => [tyr -> HM].
split; inversion. grab head_form. by inversion. move => ?.
move : (HM) => /IH. move /(_ ltac:(ssromega) w). case.
move /(_ ltac:(assumption)).
apply : unnest.
grab where eta_deficiency. move => /=.
exists_matching_typing. apply /typing_uabsP. eexists. reflexivity. eassumption. done.
move => [N [? [? ?]]] _.
exists (uabs N).
split. by auto using normal_form.
split. by rewrite typing_uabsE.
move => /=.
exists_matching_typing. apply /typing_uabsP. eexists. reflexivity. eassumption.
}
Admitted.



have : (eta_deficiency ctx M false = 0) \/ 
  (eta_deficiency ctx M false = (eta_deficiency ctx M false - 1).+1) by unfoldN; lia.
case => ->.
have : (eta_deficiency ctx N true = 0) \/ 
  (eta_deficiency ctx N true = (eta_deficiency ctx N true - 1).+1) by unfoldN; lia.
case => ->.

(*
Lemma eta_expand_OLDER : forall (M : term) (ctx : context typ) ty (w : nat), Some ty == typing ctx M -> 
  (normal_form M -> is_eta_long ctx M (w.+1) false ->
  exists N, normal_form N /\ (Some ty == (typing ctx N)) /\ is_eta_long ctx N w false) /\
  (head_form M -> is_eta_long ctx M (w.+1) true ->
  exists N, head_form N /\ (Some ty == (typing ctx N)) /\ is_eta_long ctx N w true).
Proof.
elim /(f_ind term_size).
(*better strategy: if M is in head form, then treat normal form branch uniformly by case on ty*)
move => M.
have := (nf_cases M); (case; last case).
(*M is in head form*)
admit. (*most work*)

(*M is not in head form*)
{
case : M => /=.
move => ? [? ?]. exfalso. grab where head_form. apply. auto using head_form.
move => ? ? [? ?]. grab normal_form; by inversion.
(*abs case*)
{
move => tyl M _ IH ctx ty w. move /typing_absP => [tyr -> HM].
split; inversion. grab head_form. by inversion. move => ?.
move : HM. move /IH. move /(_ ltac:(ssromega) w). case.
move /(_ ltac:(assumption) ltac:(assumption)) => [N [? [? ?]]] _.
exists (abs tyl N).
split. by auto using normal_form.
split. by rewrite typing_absE.
done.
}
move => ? ? [? ?]. grab normal_form; by inversion.
(*uabs case*)
{
move => M _ IH ctx ty w. move /typing_uabsP => [tyr -> HM].
split; inversion. grab head_form. by inversion. move => ?.
move : HM. move /IH. move /(_ ltac:(ssromega) w). case.
move /(_ ltac:(assumption) ltac:(assumption)) => [N [? [? ?]]] _.
exists (uabs N).
split. by auto using normal_form.
split. by rewrite typing_uabsE.
done.
}
}
(*M is not in normal form*)
{
intros.
split; by [ | by move /nf_hf].
}
Admitted.

case => /=.
(*var case*)
{
move => x IH ctx ty w Hx.
move : (Hx) => /eqP <-.
split => _.
(*var nf case*)
{
revert dependent ty. case => /=.
move => n Hx _. exists (var x).
split. by auto using normal_form, head_form.
split. done. 
rewrite /is_eta_long -/is_eta_long.
move : (Hx) => /eqP <-. apply /orP => //=. right. apply /leP. unfoldN. lia.

move => tyl tyr Hx ?. exists (abs tyl (app (var (x.+1)) (var 0))).
split. by auto using normal_form, head_form.
split. rewrite typing_absE. apply /typing_appP. exists tyl.
admit. (*easy shift*)
done.
rewrite /is_eta_long -/is_eta_long.
cbn.
have : ctxnth ctx x = Some (tyl ->t tyr) by admit. (*easy*)
move => ->.
have : eqtyp tyl tyl by apply /eqP. move => ->.
apply /andP. split. apply /andP. split.
apply /eqP. unfoldN. lia.
done.
apply /eqP. unfoldN. lia.

move => ty Hx ?. exists (uabs (uapp (var x) (tyvar 0))).
split. admit.
split. apply /typing_uabsP. eexists. reflexivity. apply /typing_uappP. exists (shift_typ 1 0 ty).
rewrite subst_typ_to_subst_typ_1.
admit. (*doable*)
admit. (*somehow maybe with additional shift on x*)
cbn.
have : ctxnth (ctxmap (shift_typ 1 0) ctx) x = Some (shift_typ 1 0 (tyabs ty)) by admit.
move => ->. cbn.
have : typ_size (subst_typ 0 [:: tyvar 0] (shift_typ 1 1 ty)) = typ_size ty by admit.
move => ->.
apply /andP. split => //.
}
(*var hf case*)
{
move => _. exists (var x).
split. by auto using head_form.
split => //.
cbn.
admit. (*easy*)
}
}
(*app case*)
{
move => M N IH ctx tyr.
admit. (*inspect*)
}
(*abs case*)
{
move => tyl M IH ctx ty w. move /typing_absP => [tyr -> HM].
split; inversion. grab head_form. by inversion. move => ?.
move : HM. move /IH. move /(_ ltac:(ssromega) w). case.
move /(_ ltac:(assumption) ltac:(assumption)) => [N [? [? ?]]] _.
exists (abs tyl N).
split. by auto using normal_form.
split. by rewrite typing_absE.
done.
}
(*uapp case*)
{
move => M tyl IH ctx tyr w HM. move : (HM) => /typing_uappP [ty] ?. subst. move => H'M. split.
inversion. grab head_form. inversion.
move : (HM) => /eqP <- /andP => [[? ?]]. 

admit. (*inspect*)
admit.
}
(*uabs case*)
{
move => M IH ctx ty w. move /typing_uabsP => [tyr -> HM].
split; inversion. grab head_form. by inversion. move => ?.
move : HM. move /IH. move /(_ ltac:(ssromega) w). case.
move /(_ ltac:(assumption) ltac:(assumption)) => [N [? [? ?]]] _.
exists (uabs N).
split. by auto using normal_form.
split. by rewrite typing_uabsE.
done.
}
Qed.
*)
(*
Fixpoint is_eta_long (ctx : context typ) (M : term) (w : nat) : bool :=
  match M with
  | var x => if (typing ctx M) is Some ty then eta_weight ty <= w else false
  | app M' N' => if (typing ctx M) is Some ty then (eta_weight ty <= w) && is_eta_long ctx M' (w.+1) && is_eta_long ctx N' 0 else false
  | uapp M' _ => if (typing ctx M) is Some ty then (eta_weight ty <= w) && is_eta_long ctx M' (w.+1) else false
  | abs tyl M' => is_eta_long ((Some tyl)::ctx) M' 0
  | uabs M' => is_eta_long (ctxmap (shift_typ 1 0) ctx) M' 0
  end.

?????
Lemma eta_expand : forall (M : term) (ctx : context typ) ty (w : nat), 
  normal_form M -> Some ty == typing ctx M -> is_eta_long ctx M (w.+1) ->
  exists N, normal_form N /\ (Some ty == (typing ctx N)) /\ is_eta_long ctx N w.
Proof.
elim /(f_ind term_size).
case => /=.
(*var case*)
move => x IH cty ty w ? Hx.
move : (Hx) => /eqP <- ?.
revert dependent ty. case => /=.
admit. admit. admit. (*doable*)

(*app case*)
move => M N IH cty ty w. inversion. grab head_form. inversion.
move => Hty. move : (Hty) => /eqP <-.
move : Hty => /typing_appP => [[tyl ?] ?].
case /andP. case /andP. move => ?.
move /IH. move /(_ ltac:(unfoldN; lia) _ ltac:(auto using normal_form) ltac:(eassumption)).

Qed.
*)


(*
Fixpoint is_eta_long (ctx : context typ) (M : term) : bool :=
  match M with
  | var x => if (typing ctx M) is Some (tyvar _) then true else false
  | app M' N' => if (typing ctx M) is Some (tyvar _) then is_eta_long_aux ctx M' && is_eta_long ctx N' else false
  | uapp M' _ => if (typing ctx M) is Some (tyvar _) then is_eta_long_aux ctx M' else false
  | abs tyl M' => is_eta_long ((Some tyl)::ctx) M'
  | uabs M' => is_eta_long (ctxmap (shift_typ 1 0) ctx) M'
  end
with is_eta_long_aux (ctx : context typ) (M : term) : bool :=
  match M with
  | var _ => true
  | app M' N' => is_eta_long_aux ctx M' && is_eta_long ctx N'
  | uapp M' _ => is_eta_long_aux ctx M'
  | abs tyl M' => is_eta_long ((Some tyl)::ctx) M'
  | uabs M' => is_eta_long (ctxmap (shift_typ 1 0) ctx) M'
  end.
*)

(*
MAYBE THIS ETA DECREASE IDEA IS TOO HEAVY
Fixpoint eta_deficiency (ctx : context typ) (M : term) :=
  match M with
  | var _ => 0
  | app M N => eta_deficiency ctx M + eta_deficiency ctx N
  | uapp M _ => eta_deficiency ctx M
  | abs tyl M => (eta_deficiency (Some tyl :: ctx) M) + 
    if is_head_form M then
      if (typing (Some tyl :: ctx) M) is Some tyr then eta_weight tyr else 0
    else 0
  | uabs M => (eta_deficiency (ctxmap (shift_typ 1 0) ctx) M) + 
    if is_head_form M then
      if (typing (ctxmap (shift_typ 1 0) ctx) M) is Some ty then eta_weight ty else 0
    else 0
  end.








Lemma eta_deficiency_decrease : forall (M : term) (ctx : context typ) (ty : typ), 
  normal_form M -> (Some ty == (typing ctx M)) -> eta_deficiency ctx M > 0 -> 
  exists N, normal_form N /\ (Some ty == (typing ctx N)) /\ eta_deficiency ctx N < eta_deficiency ctx M.
Proof.
elim /(f_ind term_size).
move => M IH ctx ty. inversion.
(*M is in head form*)
admit.

(*M is an abstraction*)
{
match goal with [M' : term |- _] => rename M' into M end.
move /typing_absP => [tyr ?]. subst => /=.
move => HM. move : (HM) => /eqP => <-.
move H_hf_M : (is_head_form M) => h.
case : h H_hf_M => ?.
(*body of M is in head form*)
{
revert dependent tyr. case => /=.
(*body of M is of atomic type*)
move => n ?.
simpl_natarith.
move /IH => /=. move /(_ ltac:(unfoldN; lia) _ ltac:(auto using normal_form) ltac:(eassumption)).
move => [N [? [HN ?]]]. exists (abs t N).
split. by auto using normal_form.
split. by rewrite typing_absE.
rewrite /eta_deficiency -/eta_deficiency.
move : (HN) => /eqP <- /=.
case : (is_head_form N); apply /eqP; unfoldN; lia.
(*body of M is of arrow type*)
move => tyl tyr HM.
rewrite <- (@subject_reduction_proof.typing_shift _ 0 _ [:: Some tyl]) in HM.
have : ([:: Some tyl, Some t & ctx] \|- shift_term 1 0 M \: tyl ->t tyr) by assumption.
move => {HM}HM.
exists (abs t (abs tyl (app (shift_term 1 0 M) (var 0)))).
split. do 2 apply nf_abs. admit. (*doable*)
split. do 2 rewrite -> typing_absE. apply /typing_appP. exists tyl => //.


rewrite /eta_deficiency -/eta_deficiency /is_head_form -/is_head_form.
rewrite /typing /typing_rec -/typing_rec -/typing.
move : (HM) => /eqP <- /=.
have : (Some tyl == Some tyl) by apply /eqP. move => ->. admit. (*kind of doable*)










(*OLD approach*)
revert dependent M. case => //=.
(*var case*)
case : tyr => /=.
(*case tyr is tyvar*)
intros. unfoldN. by lia.
(*case tyr is tyfun*)
move => tyl tyr n IH ? ? _ ?.
exists (abs t (abs tyl (app (var (n.+1)) (var 0)))).
split. do 2 apply nf_abs. by auto using normal_form, head_form.
split. do 2 rewrite -> typing_absE. apply /typing_appP. exists tyl => //.
move => /=.
grab where (Some t). move /eqP. cbn => <-.
have : (eqtyp tyl tyl = true) by apply /eqP. move => ->.
apply /eqP. unfoldN. by lia.
(*case tyr is tyabs*)
move => tyr n IH ? ? _ _.
exists (abs t (uabs (uapp (var (n.+1)) (tyvar 0)))).



move => n IH ? ? _.

inversion M.

move => ?.



have : (0 < eta_deficiency (Some t :: ctx) M)%coq_nat \/ (0 < eta_weight tyr)%coq_nat.
unfoldN. grab where is_head_form. case : (is_head_form M) => ?; lia.
case.
move /leP /IH => /=. move /(_ ltac:(ssromega) _ ltac:(assumption) ltac:(eassumption)).
move => [N [? [? ?]]].
exists (abs t N). split; first by auto using normal_form.
split; first by rewrite typing_absE.
rewrite /eta_deficiency -/eta_deficiency.

 by unfoldN; lia.

move Hh : (is_head_form M) => h.
case : h Hh.
*)

Lemma f_eta_long : ???


(*NEXT: if there is a derivation, then there is a ipc2 long derivation*)
(*deed induction on term size*)
Lemma f_to_normal_derivation : forall t Gamma M labeling, bijective labeling -> 
  (Some (formula_to_typ labeling 0 t) == typing (map (fun t => Some (formula_to_typ labeling 0 t)) Gamma) M) ->
  well_formed_formula t -> Forall well_formed_formula Gamma -> normal_form M -> exists d, normal_derivation d Gamma t.
Proof.
elim /(@f_ind _ formula_size).
case.

admit. (*easy*)

move => a _ Gamma M labeling ? ? ? ?.
inversion.
grab head_form. move /f_hf_to_partial_chain. 
move /(_ _ _ _ _ _ _ ltac:(eassumption)). move /(_ ltac:(assumption) ltac:(assumption) ltac:(constructor)) => [s [ts [? [? ?]]]].
(*more work is needed because induction is suddenly on term size*)
admit.
grab where abs. move /typing_absP => [? ?]. done.
grab where uabs. move /typing_uabsP => [? ?]. done.

move => tyl tyr IH.





