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

Ltac unfoldN := do ?unfold addn, subn, muln, addn_rec, subn_rec, muln_rec, Equality.sort, nat_eqType in *.

Ltac inspect_eqn := try (
  match goal with
  | [ |- context [eqn ?x ?y]] => 
    do [(have : x <> y by unfoldN; lia); move /eqP /negbTE; let H := fresh in move => H; cbn in H; move : H => -> |
     (have : x = y by unfoldN; lia); move /eqP; let H := fresh in move => H; cbn in H; move : H => ->]
  end).

Inductive normal_form : term -> Prop :=
  | nf_hf : forall M, head_form M -> normal_form M
  | nf_abs : forall t M, normal_form M -> normal_form (abs t M)
  | nf_uabs : forall M, normal_form M -> normal_form (uabs M)
with head_form : term -> Prop :=
  | hf_var : forall n, head_form (var n)
  | hf_app : forall t1 t2, head_form t1 -> normal_form t2 -> head_form (app t1 t2)
  | hf_uapp : forall t1 s, head_form t1 -> head_form (uapp t1 s).

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

(*
Lemma not_reducible_normal_form : forall t, (negb (is_reducible t)) -> normal_form t.
Proof.
move => t.
move Hn : (term_size t) => n.
move : n t Hn.
elim /lt_wf_ind => n IH.
case.

{ intros. do 2 constructor. }
{
cbn.
move => t1 t2 ?.
(*move /negP.*)
rewrite ? negb_or.
move /andP.
case.
move /andP.
case.
intros.
have : normal_form t1.
apply : IH => //. ssromega.

have : normal_form t2.
apply : IH => //. ssromega.

move => ? RR. case : RR a.
intros. constructor. by constructor.
cbn. discriminate.

admit. (*ugh, here we need actual typing?*)

intros. constructor. constructor => //.
admit. (*doable in principle, need to adjust normal_form*)
}

{
intros. apply : nf_abs. constructor. constructor.


constructor.

nia.
move : (term_size t1) => m.
  lia.

move /negP.
move => [? ?].
apply /andP.

rewrite /negb.

cbn.

have : is_true (is_abs t1 || is_reducible t1) by admit.
move /orP.

rewrite /orP.


case.
move /boolP.
prop_congr.
Check is_true.
Locate is_true.
move /negb_prop_intro.

destr_bool.

firstorder.
case.

case.
{ cbn. intros. constructor. constructor. constructor. apply : IH => //. lia. }
{ move => t1 t2 t3. rewrite /is_reducible. move : (t1 @ t2) => t.

move => t1 t2.
cbn.


exfalso.

apply H.
cbn.

eauto.
*)


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

Fixpoint formula_to_typ (labeling : label -> nat) (t : formula) : typ :=
  match t with
  | Formula.var x => tyvar x
  | atom a => tyvar (labeling a)
  | arr s t => tyfun (formula_to_typ labeling s) (formula_to_typ labeling t)
  | quant t => tyabs (formula_to_typ (fun a => 1 + labeling a) t)
  end.

(*
(*atoms point to larger indices*)
Fixpoint typ_to_formula (n : nat) (t : typ) : formula :=
  match t with
  | tyvar x => if x > n then atom (0, x-n) else Formula.var x
  | tyfun s t => arr (typ_to_formula n s) (typ_to_formula n t)
  | tyabs t => quant (typ_to_formula (1+n) t)
  end.

(*TODO: reformulate using map from labels to vars*)
(*atoms point to larger indices*)
Fixpoint formula_to_typ (n : nat) (t : formula) : typ :=
  match t with
  | Formula.var x => tyvar x
  | atom (_, x) => tyvar (n+x)
  | arr s t => tyfun (formula_to_typ n s) (formula_to_typ n t)
  | quant t => tyabs (formula_to_typ (1+n) t)
  end.
*)

(*Definition type_environment_to_basis (ctx : context typ) : list formula : (map (omap (typ_to_formula 0)) ctx).*)

(*
Lemma f_to_ipc : forall t (ty : typ) Gamma, 
 normal_form t -> (Some ty == typing (map (fun t => Some (formula_to_typ t)) Gamma) t) -> 
 exists n, normal_derivation n Gamma (typ_to_formula 0 ty).
*)


Lemma in_to_index : forall t Gamma, In t Gamma -> exists n, forall labeling, ctxindex (map (fun t => Some (formula_to_typ labeling t)) Gamma) n (formula_to_typ labeling t).
Proof.
move => t. elim => //.
move => s Gamma IH.
case /in_cons_iff.

move => ?. subst. by exists 0.

move /IH => [n ?]. by exists (1+n).
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
    | tyvar n => tyvar (if a == n then c else (if c <= n then n.+1 else n))
    | tl ->t tr => shift_typ_0 a c tl ->t shift_typ_0 a c tr
    | tyabs t => tyabs (shift_typ_0 (a.+1) (c.+1) t)
  end.

(*not final, need shift_typ 1 0 with 0 <> n*)
Lemma shift_typ_0_shift : forall a ty n, shift_typ 1 n (shift_typ_0 (n + a) n ty) = shift_typ_0 (1 + n + a) (1 + n) (shift_typ 1 n ty).
Proof.
move => a.
elim; cbn.

move => m n.
have : (m >= n)%coq_nat \/ (m < n)%coq_nat by lia. case => ?.
have : (m + 1)%Nrec = m.+1 by unfoldN; lia. move => ->.
have : ((n + a)%coq_nat = m) \/ ((n + a)%coq_nat <> m) by lia. case => ?.

1-2: do ? inspect_eqn; unfoldN; f_equal; lia.
do ? inspect_eqn.
revert dependent m. case => //.
intros. by do ? inspect_eqn.

intros; f_equal; auto.
move => ? IH ?. f_equal. apply : IH.
Qed.

Lemma shift_typ_0_subst : forall a n m tyr tyl, shift_typ_0 a n (subst_typ m [:: tyr] tyl) = subst_typ m [:: shift_typ_0 a n tyr] (shift_typ_0 a (1 + n) tyl).
Admitted.


Lemma shift_typ_0_preserves_typing a n ctx t ty : 
  ctx \|- t \: ty ->
  ctxmap (shift_typ_0 (n+a) n) ctx \|-
    typemap (shift_typ_0 (n+a)) n t \: shift_typ_0 (n+a) n ty.
Proof.
elim: t a ty n ctx =>
  [m | tl IHtl tr IHtr | tyl t IHt | t IHt tyr | t IHt] a ty n ctx /=.
- by apply ctxindex_map.
- by case/typing_appP => tyl H H0; apply/typing_appP;
    exists (shift_typ_0 (n+a) n tyl); [apply (IHtl a (tyl ->t ty)) | apply IHtr].
- by case/typing_absP => tyr -> H; rewrite /= typing_absE; move: H; apply IHt.
- case/typing_uappP => tyl -> H; apply/typing_uappP;
    exists (shift_typ_0 (1+n+a) (1+n) tyl).
  + admit. (* apply shift_typ_0_subst.*)
  + by move: H; apply IHt.
- case/typing_uabsP => ty' -> H; rewrite /= typing_uabsE.
  move : H. move /IHt.
  apply : (eq_ind IHt).

  suff ->: ctxmap (shift_typ 1 n) (ctxmap (shift_typ_0 (n+a) n) ctx) =
           ctxmap (shift_typ_0 (1+n+a) (1+n)) (ctxmap (shift_typ 1 n) ctx) by
    admit. (*apply IHt.*)
  clear; rewrite -!map_comp; apply eq_map; case => //= ty''; f_equal. apply : shift_typ_0_shift.



Lemma shift_typ_0_preserves_typing a n ctx t ty : n <= a ->
  ctx \|- t \: ty ->
  ctxmap (shift_typ_0 a n) ctx \|-
    typemap (shift_typ_0 a) n t \: shift_typ_0 a n ty.
Proof.
elim: t ty n ctx =>
  [m | tl IHtl tr IHtr | tyl t IHt | t IHt tyr | t IHt] ty n ctx ? /=.
- by apply ctxindex_map.
- by case/typing_appP => tyl H H0; apply/typing_appP;
    exists (shift_typ_0 a n tyl); [apply (IHtl (tyl ->t ty)) | apply IHtr].
- by case/typing_absP => tyr -> H; rewrite /= typing_absE; move: H; apply IHt.
- case/typing_uappP => tyl -> H; apply/typing_uappP;
    exists (shift_typ_0 a (1+n) tyl).
  + apply shift_typ_0_subst.
  move : H. move /IHt. move /(_ n ltac:(assumption)). apply. cbn. 
  + by move: H; apply IHt.
- case/typing_uabsP => ty' -> H; rewrite /= typing_uabsE.
  suff ->: ctxmap (shift_typ 1 0) (ctxmap (shift_typ_0 a n) ctx) =
           ctxmap (shift_typ_0 a (1+n)) (ctxmap (shift_typ 1 0) ctx) by
    apply IHt.
  clear; rewrite -!map_comp; apply eq_map; case => //= ty''; f_equal; apply shift_typ_0_shift.

Admitted. (* TODO: REDO because shift typ needs to increase under abs
elim: t ty n ctx =>
  [m | tl IHtl tr IHtr | tyl t IHt | t IHt tyr | t IHt] ty n ctx /=.
- by apply ctxindex_map.
- by case/typing_appP => tyl H H0; apply/typing_appP;
    exists (shift_typ_0 a n tyl); [apply (IHtl (tyl ->t ty)) | apply IHtr].
- by case/typing_absP => tyr -> H; rewrite /= typing_absE; move: H; apply IHt.
- case/typing_uappP => tyl -> H; apply/typing_uappP;
    exists (shift_typ_0 a (1+n) tyl).
  + apply shift_typ_0_subst.
  move : H. move /IHt. 
  + by move: H; apply IHt.
- case/typing_uabsP => ty' -> H; rewrite /= typing_uabsE.
  suff ->: ctxmap (shift_typ 1 0) (ctxmap (shift_typ_0 a n) ctx) =
           ctxmap (shift_typ_0 a (1+n)) (ctxmap (shift_typ 1 0) ctx) by
    apply IHt.
  clear; rewrite -!map_comp; apply eq_map; case => //= ty''; f_equal; apply shift_typ_0_shift.
Qed.*)

Fixpoint subst_typ_1 n s t := 
  match t with
    | tyvar m => if n == m then (shift_typ n 0 s) else if n < m then tyvar (m-1) else tyvar m
    | tl ->t tr => subst_typ_1 n s tl ->t subst_typ_1 n s tr
    | tyabs t => tyabs (subst_typ_1 n.+1 s t)
  end.




Lemma labeling_ext : forall t labeling1 labeling2, (forall a, labeling1 a = labeling2 a) -> formula_to_typ labeling1 t = formula_to_typ labeling2 t.
Proof.
elim; cbn; intros; f_equal; eauto.
Qed.

Lemma subst_typ_to_subst_typ_1 : forall s t n, subst_typ n [:: s] t = subst_typ_1 n s t.
Proof.
move => s. elim; cbn.
move => n m.
have : (m = n) \/ (lt m n) \/ (lt n m) by lia.
case; last case.
move => ?. subst.
do ? inspect_eqn.
have : (n - n)%Nrec = 0 by unfoldN; lia. by move => ->.

move => ?.
have : n = (n-1).+1 by unfoldN; lia. move => ->.
do ? inspect_eqn.
have : ((n - 1).+1 - m)%Nrec = (n - 1 - m).+1 by unfoldN; lia. move => ->. cbn.
move : {2}((n - 1)%Nrec - m)%Nrec => d. case : d; cbn; unfoldN; intros; f_equal; lia.

move => ?.
do ? inspect_eqn.
revert dependent n. case; cbn => // n ?. by inspect_eqn.

all: intros; f_equal; eauto.
Qed.

Lemma instantiate_subst_typ_eq : forall labeling s n t, lc 0 t -> lc (n.+1) s -> (forall a, n <= labeling a) -> formula_to_typ labeling (instantiate t n s) = subst_typ n [:: formula_to_typ (fun a => labeling a - n) t] (formula_to_typ (fun a : label => (labeling a).+1) s).
Proof.
move => labeling s n t Ht.
rewrite subst_typ_to_subst_typ_1.
elim : s labeling n.

move => m labeling n. inversion. cbn. move => H.
have : (m = n) \/ (m < n)%coq_nat by lia. case.
move => ?. subst.
inspect_eqb. inspect_eqn.
admit. (*doable*)

move => ?.
inspect_eqb. inspect_eqn. cbn.
revert dependent m. case; cbn => //.
intros. by inspect_eqn.

cbn. move => a labeling n _ /(_ a).
move /eqP. cbn. move => ?.
do ? inspect_eqn.
unfoldN. f_equal. lia.

cbn. intros. grab lc. inversion. f_equal; eauto.

cbn. move => s IH labeling n. inversion. move => Hl. f_equal. 
grab lc. move /IH. move /(_ (fun a : label => (labeling a).+1) (ltac:(eassumption))).
apply.
Admitted.

Lemma bind_shift_eq : forall a t labeling n, injective labeling -> lc n t -> (forall b, labeling b >= n) ->
  formula_to_typ (fun b : label => (labeling b).+1) (bind a n t) = shift_typ_0 (labeling a) n (formula_to_typ (fun b => labeling b) t).
Proof.
move => a. elim; cbn.
move => m labeling n _. inversion. move /(_ a) /eqP => ?.
by do ? inspect_eqn.

move => b labeling n Il _ Hl.
have := (Hl a). move /eqP => ?. 
have := (Hl b). move /eqP => ?. 
case : (Label.eq_dec a b).
move => H. move : (H) => /Label.eqb_eq ->.
subst. inspect_eqn. done.

move => H. move : (H) => /Label.neq_neqb ->.
have ? : labeling a <> labeling b by auto.
do ? inspect_eqn. done.

by intros; grab lc; inversion; f_equal; auto.

move => t IH labeling n *. f_equal. grab lc. inversion.
apply : IH; cbn => //.
grab injective. clear.
move => ? a b ?. have : (labeling a) = (labeling b) by lia.
auto.
Qed.


Lemma shift_typ_0_fresh : forall a t labeling n, injective labeling -> fresh_in a t -> lc n t -> (forall b, n <= labeling b) ->
  shift_typ 1 n (formula_to_typ labeling t) = shift_typ_0 (labeling a) n (formula_to_typ labeling t).
Proof.
move => a. elim.
move => m labeling n _ _. inversion. move => /(_ a) /eqP => ?.
cbn. by do ? inspect_eqn.

move => b labeling n ?. inversion. move => _ H.
move : (H a) => /eqP => ?. move : (H b) => /eqP => ?.
cbn. have ? : labeling a <> labeling b by auto. do ? inspect_eqn. f_equal. unfoldN. lia.

cbn; intros; grab lc; inversion; grab fresh_in; inversion; f_equal; auto.

cbn. move => t IH labeling n *.
grab lc; inversion; grab fresh_in; inversion.
f_equal.
apply : IH => //.
move => x y ?. have : labeling x = labeling y by lia. auto.
Qed.


(*doable, needs renaming lemmas on iipc2 and derivation depth*)
(*exists labeling is wrong because of branches*)
Lemma iipc2_to_f : forall Gamma t, iipc2 Gamma t -> forall labeling, injective labeling -> exists M, (Some (formula_to_typ labeling t) == typing (map (fun t => Some (formula_to_typ labeling t)) Gamma) M).
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
move : (HM ltac:(eassumption) ltac:(eassumption)) => [M ?].
move : (HN ltac:(eassumption) ltac:(eassumption)) => [N ?].
exists (app M N). apply /typing_appP. eexists; eauto.
(*admit.*) (*easy*)
(*exists (app M N). move => n. apply /typing_appP. eexists; eauto.*)
}

(*abs case*)
{
move => s t _ HM labeling ?.
move : (HM ltac:(eassumption) ltac:(eassumption)) => [M ?].
exists (abs (formula_to_typ labeling s) M).
apply /typing_absP. by eexists.
}

(*uapp case*)
(*labeling has to come before exists, otherwise there is no one single solution term*)
{
move => s t ? /iipc2_wff. case => ?. inversion. move => HM labeling ?.
move : (HM ltac:(eassumption) ltac:(eassumption)) => [M ?].
exists (uapp M (formula_to_typ labeling t)).
apply /typing_uappP.
eexists; try eassumption.
rewrite -/formula_to_typ.
rewrite instantiate_subst_typ_eq => //.
do 2 f_equal.
apply : labeling_ext. intro. unfoldN; lia.
}

(*uabs case*)
{
move => t a ? ? HM labeling ?.
(*problem : a is abstracted, but I need (0,0) abstracted next. need renamings and induction on derivation depth*)
move : HM. move /(_ ltac:(eassumption) ltac:(eassumption)) => [M].
move /(@shift_typ_0_preserves_typing (labeling a) 0).
move /(_ ltac:(auto)) => HM.

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


(*NEXT: if there is a derivation, then there is a ipc2 long derivation*)


