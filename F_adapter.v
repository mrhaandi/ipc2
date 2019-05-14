Require Import List.
Require Import ListFacts.
Require Import Arith.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import Formula.
Require Import FormulaFacts.
From LCAC Require Import Relations_ext seq_ext_base ssrnat_ext seq_ext F.
Require Import UserTactics.
Require Import Derivations.
Require Import DerivationDepth.
Require Import IIPC2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Wf_nat.
Require Import Psatz.


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


(*if h is true, then the outermost type matters for head form*)
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


(*signifies that D |> ctx |- M : ty and M is beta normal and eta long wrt D*)
Inductive normal_long_derivation (ctx : context typ) (M : term) (ty : typ) : Prop :=
  | nld_intro : Some ty == typing ctx M -> normal_form M -> eta_deficiency ctx M true = 0 -> normal_long_derivation ctx M ty.


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
elim /(f_ind term_size).

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
elim /(f_ind term_size).
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

intros * => ?. case /Forall_cons_iff => ? ? ?. move /eqP. case.
move /formula_to_typ_injective. auto.

intros * => ?. case /Forall_cons_iff => ? ? ?.
move /IH. auto.
Qed.

(*increases all free type variables by 1 except a which is set to zero*)
Fixpoint shift_typ_0 (a : nat) c t :=
  match t with
    | tyvar n => tyvar (if c+a == n then c else (if c <= n then n.+1 else n))
    | tl ->t tr => shift_typ_0 a c tl ->t shift_typ_0 a c tr
    | tyabs t => tyabs (shift_typ_0 a (c.+1) t)
  end.


Lemma shift_typ_0_shift : forall a m ty n d, d <= n ->
  shift_typ_0 a (m + n) (shift_typ m d ty) = shift_typ m d (shift_typ_0 a n ty).
Proof.
move => a m. elim => /=.
move => n' n d ?.
have : (d <= n')%coq_nat \/ (d > n')%coq_nat by lia.
case => ?; do ? inspect_eqn => //.
have : (n + a = n')%coq_nat \/ (n + a <> n')%coq_nat by lia.
case => ?; do ? inspect_eqn; try (f_equal; unfoldN; lia).
have : (n <= n')%coq_nat \/ (n > n')%coq_nat by lia.
case => ?; do ? inspect_eqn => //.

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


Lemma subst_typ_to_subst_typ_1 : forall s t n, subst_typ n [:: s] t = subst_typ_1 n s t.
Proof.
move => s. elim => /=.
move => n m.
have : (m = n) \/ (lt m n) \/ (lt n m) by lia.
(case; last case) => ?.

subst. do ? inspect_eqn.
have : (n - n) = 0 by unfoldN; lia. by move => ->.

do ? inspect_eqn. move => /=.

have : (n - m) = (n - m - 1).+1 by ssromega. move => -> /=.
move : {2}(n - m - 1) => d. case : d; cbn; unfoldN; intros; f_equal; lia.

by do ? inspect_eqn.

all: intros; f_equal; eauto.
Qed.


Lemma shift_typ_0_subst : forall a d tyr tyl m,
  shift_typ_0 a (m+d) (subst_typ_1 m tyr tyl) = subst_typ_1 m (shift_typ_0 a d tyr) (shift_typ_0 a (m+d).+1 tyl).
Proof.
move => a d tyr. elim => /=.

move => n' m.
have : (m = n') \/ (m < n')%coq_nat \/ (m > n')%coq_nat by lia.
(case; last case) => ?; do ? inspect_eqn.
subst. apply : shift_typ_0_shift. ssromega.

have : ((d + m).+1 + a = n') \/ ((d + m).+1 + a <> n') by lia.
case => ?; do ? inspect_eqn.
subst => /=. f_equal. do ? inspect_eqn. unfoldN. lia.
have : (d + m < n')%coq_nat \/ (d + m >= n')%coq_nat by lia.
case => ?; do ? inspect_eqn.
1-3: move => /=; do ? inspect_eqn; f_equal; unfoldN; lia.


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
move => labeling m. elim => /=; intros; grab lc; inversion; f_equal; auto.

by inspect_eqn.

inspect_eqn. unfoldN. by lia.
grab lc. grab where formula_to_typ. move => IH /IH. auto.
Qed.


Lemma instantiate_subst_typ_eq : forall labeling s n t, lc 0 t -> lc (n.+1) s -> 
  formula_to_typ labeling n (instantiate t n s) = subst_typ_1 n (formula_to_typ labeling 0 t) (formula_to_typ labeling (n.+1) s).
Proof.
move => labeling s n t Ht.
elim : s n => /=.

move => m n. inversion.
have : (m = n) \/ (m < n)%coq_nat by lia. case => ?.
subst.
inspect_eqb. inspect_eqn.
by apply : (@labeling_shift_typ_eq _ _ _ 0).

inspect_eqb. inspect_eqn. move => /=.
by inspect_eqn.

move => a n _.
do ? inspect_eqn.
unfoldN. f_equal. by lia.

intros. grab lc. inversion. f_equal; eauto.

move => s IH n. inversion. f_equal. eauto.
Qed.


Lemma bind_shift_eq : forall a t labeling n, injective labeling -> lc n t ->
  formula_to_typ labeling (n.+1) (bind a n t) = shift_typ_0 (labeling a) n (formula_to_typ labeling n t).
Proof.
move => a. elim => /=.
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
move => a. elim => /=.
move => m labeling n _ _. inversion.
by do ? inspect_eqn.

move => b labeling n ?. inversion. move => _.
have ? : labeling a <> labeling b by auto. do ? inspect_eqn. f_equal. unfoldN. by lia.

intros; grab lc; inversion; grab fresh_in; inversion; f_equal; auto.

move => t IH labeling n *.
grab lc; inversion; grab fresh_in; inversion.
f_equal.
apply : IH => //.
Qed.


(*if there is an iipc2 derivation, then there is a corresponding system F typing*)
Theorem iipc2_to_f : forall Gamma t, iipc2 Gamma t -> forall labeling, injective labeling -> exists M, (Some (formula_to_typ labeling 0 t) == typing (map (fun t => Some (formula_to_typ labeling 0 t)) Gamma) M).
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

grab Forall. grab Forall. grab injective. clear => ?.
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
intros *; inversion.
apply : partial_chain_cons; try eassumption + constructor.
constructor.

move => t' ts IH.
intros *; inversion.
apply : partial_chain_cons; try eassumption.
by apply IH.
Qed.


Lemma contains_transitivity : forall s t u, contains s t -> contains t u -> contains s u.
Proof.
intros *; elim => //.
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
intros *. inversion. by inspect_eqn.
intros * => _. inspect_eqn. f_equal. unfoldN. lia.
intros. grab lc. inversion. f_equal; auto.
intros. grab lc. inversion. f_equal.
have : (m + n).+1 = (m.+1 + n) by unfoldN; lia. move => ->. auto.
Qed.


(*pulls out typing expressions out of match*)
Ltac exists_matching_typing := 
  match goal with [|- context[match typing ?ctx ?M with | Some _ => _ | None => _ end]] => 
    let ty := fresh "ty" in evar (ty : typ); let ty' := eval red in ty in 
      (have : Some ty' == typing ctx M); last ((move => /eqP <-); subst ty); try eassumption end.


Lemma f_hf_to_partial_chain : forall labeling, bijective labeling -> forall M Gamma t, 
  Forall well_formed_formula Gamma -> well_formed_formula t ->
  let ctx := (map (fun t => Some (formula_to_typ labeling 0 t)) Gamma) in
  head_form M -> Some (formula_to_typ labeling 0 t) == typing ctx M -> eta_deficiency ctx M false = 0 ->
  exists s ts, In s Gamma /\ partial_chain s t ts /\ 
    (Forall (fun t' => exists M', term_size M' < term_size M /\ normal_long_derivation ctx M' (formula_to_typ labeling 0 t')) ts).
Proof.
move => labeling Hl.
elim /(f_ind term_size).
move => M IH Gamma t ? ? ctx. inversion.

(*var case*)
{
rewrite typing_varE. move /index_to_in.
move /(_ ltac:(auto using bij_inj) ltac:(assumption) ltac:(assumption)) => ?.
eexists. exists [::]. split. by eassumption.
split; do ? constructor.
}

(*app case*)
{
move => Ht /=. exists_matching_typing. move => ?.
move : (Ht) => /typing_appP => [[tyl]].
have [s [-> ?]] := (@typ_to_formula tyl labeling 0 ltac:(assumption)).
move /(@IH _ _ _ (Formula.arr s t)) => /=.
move /(_ ltac:(unfoldN; lia) ltac:(assumption) ltac:(by constructor) ltac:(assumption)).
apply : unnest. unfoldN. rewrite -/ctx. lia.
move => [s' [ts' [? [? ?]]]] ?.
exists s', (ts' ++ [::s]). split. done.
split. by apply : partial_chain_arr.
rewrite Forall_app_iff. split.
grab Forall. apply : Forall_impl.
clear => t [M [? [? ?]]].
exists M. split. apply /leP. unfoldN. lia.
by constructor.

constructor; last done.
eexists. split; first last.
constructor; try eassumption.
unfoldN. by lia.
apply /leP. unfoldN. by lia.
}

(*uapp case*)
{
move => Ht /=. exists_matching_typing. move => ?.
move : (Ht) => /typing_uappP => [[tyl]]. rewrite subst_typ_to_subst_typ_1.
have [s' [-> ?]] := (@typ_to_formula tyl labeling 1 ltac:(assumption)).
move => ?.
move /(@IH _ _ _ (Formula.quant s')) => /=.
move /(_ ltac:(unfoldN; lia) ltac:(assumption) ltac:(by constructor) ltac:(assumption)).
apply : unnest. rewrite -/ctx. unfoldN. by lia.
move => [s'' [ts'' [? [? ?]]]].
exists s'', ts''. split. done.
split.
apply : partial_chain_contains; eauto.
have [s [? ?]]:= typ_to_formula ty 0 ltac:(eassumption). subst.
grab where subst_typ_1. rewrite <- instantiate_subst_typ_eq => //.
move /formula_to_typ_injective. move /(_ ltac:(auto using bij_inj) ltac:(auto using Lc.instantiate_pred) ltac:(assumption)).
move => <-. apply : contains_trans; first last; [constructor | done].
grab Forall. apply : Forall_impl.
move => ? [M' [? ?]].
exists M'. split. apply /leP. unfoldN. by lia.
done.
}
Qed.


Fixpoint is_head_form (M : term) : bool :=
  match M with
  | var _ => true
  | app M _ | uapp M _ => is_head_form M
  | _ => false
  end.


Lemma shift_typing : forall ctx ty M, typing (Some ty :: ctx) (shift_term 1 0 M) = typing ctx M.
Proof.
intros.
have := @subject_reduction_proof.typing_shift M 0 ctx [:: Some ty].
cbn => <-. f_equal. clear. rewrite /insert. cbn.
case: ctx; reflexivity.
Qed.


Lemma subt_typ_id : forall ty (n : nat), subst_typ_1 n (tyvar 0) (shift_typ 1 (n.+1) ty) = ty.
Proof.
elim => /=.
move => x n.
have : (n < x)%coq_nat \/ (n = x)%coq_nat \/ (n > x)%coq_nat by lia.
(case; last case) => ?; do ? inspect_eqn; f_equal; unfoldN; lia.
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


Lemma typ_size_pos_2 : forall ty, typ_size ty = (typ_size ty - 1) + 1.
Proof.
elim => /=; intros; unfoldN; lia.
Qed.


Lemma eta_expand_rec : forall (M : term) (ctx : context typ) (ty : typ) (w : nat), Some ty == typing ctx M -> 
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
revert dependent ty. clear.
{
case.
(*target is tyvar case*)
{
move => n ? _. exists (var x) => /=. 
split. do 2 constructor.
split. done.
exists_matching_typing => /=. done.
}
(*target is tyfun case*)
{
move => tyl' ty Hty /=. exists_matching_typing => /= ?.
pose L := (abs tyl' (shift_term 1 0 (var x) @ 0)).
have HL : Some (tyfun tyl' ty) == typing ctx L.
apply /typing_absP. eexists. reflexivity. apply /typing_appP.
eexists. rewrite shift_typing. eassumption. done.

exists L.
split. apply nf_abs. apply nf_hf. apply hf_app; [apply : shift_head_form | ]; auto using head_form, normal_form.
split. done.
move => /=. 
exists_matching_typing.
exists_matching_typing. move : HL. rewrite typing_absE => ?. eassumption.
exists_matching_typing. move : Hty. rewrite <- (@shift_typing _ tyl') => ?. eassumption.
apply /leP. unfoldN. by lia.
}
(*target is tyabs case*)
{
move => ty Hty /=. exists_matching_typing => /= ?.
pose L := (uabs ((typemap (shift_typ 1) 0 (var x)) @' 0)).
have HL : Some (tyabs ty) == typing ctx L.
apply /typing_uabsP. eexists. reflexivity. apply /typing_uappP.
eexists; first last. rewrite subject_reduction_proof.typing_shifttyp.
move : Hty => /eqP <-. apply /eqP. cbn. reflexivity.
rewrite subst_typ_to_subst_typ_1. by rewrite subt_typ_id.

exists L.
split. apply nf_uabs. apply nf_hf. apply hf_uapp.
apply map_head_form. auto using head_form.

split. done.
move => /=.
exists_matching_typing.
exists_matching_typing. move : HL. rewrite typing_uabsE => ?. eassumption.
have -> : var x = typemap (shift_typ 1) 0 x by reflexivity.
exists_matching_typing.

rewrite subject_reduction_proof.typing_shifttyp. move : Hty => /eqP <-. cbn. apply /eqP. reflexivity.
apply /leP. unfoldN. by lia.
}
}
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
{
move => n ? HM /=. nat_norm.
have : (eta_deficiency ctx M false = 0) \/ (eta_deficiency ctx M false = ((eta_deficiency ctx M false).-1).+1) by lia.
case.

move /duplicate => [? ->]. nat_norm => ?.
move : HN => /IH /=. move /(_ ltac:(unfoldN; lia) w). case. move /(_ ltac:(assumption) ltac:(assumption)).
move => [N' [? [? ?]]] _.
exists (M @ N') => /=.
split. by do 2 constructor.
have ? : Some (tyvar n) == typing ctx (M @ N'). 
apply /typing_appP. eexists; eassumption.
split. done.
exists_matching_typing => /=.
apply /leP. unfoldN. by lia.

move => ?. nat_norm => ?.
move : HM => /IH /=. move /(_ ltac:(unfoldN; lia) ((eta_deficiency ctx M false).-1)). case. move => _. move /(_ ltac:(assumption) ltac:(apply /leP; unfoldN; lia)).
move => [M' [? [? ?]]].
exists (M' @ N) => /=.
split. by do 2 constructor.
have ? : Some (tyvar n) == typing ctx (M' @ N). 
apply /typing_appP. eexists; eassumption.
split. done.
exists_matching_typing => /=.
apply /leP. unfoldN. by lia.
}
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
(*target is tyabs case*)
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
move => M tyl IH ctx ty w /duplicate [?] /typing_uappP [ty'] ? ? /=. 
exists_matching_typing. split; inversion.
(*nf case*)
grab head_form. inversion.
have : (eta_deficiency ctx M false = 0) \/ (eta_deficiency ctx M false = ((eta_deficiency ctx M false).-1).+1) by lia.
case => ?.

(*inspect ty*)
{
revert dependent ty. case.
(*target is tyvar case*)
{
move => n ? HM _ /=.
exists (M @' tyl) => /=.
split. by do 2 constructor.
have ? : Some (tyvar n) == typing ctx (M @' tyl).
apply /typing_uappP. eexists; eassumption.
split. done.
exists_matching_typing => /=.
apply /leP. unfoldN. by lia.
}
(*target is tyfun case*)
{
move => tyl' ty Hty HM.
pose L := (abs tyl' (shift_term 1 0 (M @' tyl) @ 0)).
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
(*target is tyabs case*)
{
move => ty Hty HM.
pose L := (uabs ((typemap (shift_typ 1) 0 (M @' tyl)) @' 0)).
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
have -> : typemap (shift_typ 1) 0 M @' (shift_typ 1 0 tyl) = typemap (shift_typ 1) 0 (M @' tyl) by reflexivity.
rewrite subject_reduction_proof.typing_shifttyp. move : Hty => /eqP <-. cbn. apply /eqP. reflexivity.
rewrite -> ? eta_shift_typ.
have ? := typ_size_pos ty. apply /leP. unfoldN. by lia.
}
}

grab where typing. move /IH => /=. move /(_ ltac:(ssromega) ((eta_deficiency ctx M false).-1)).
case => _. move /(_ ltac:(assumption) ltac:(apply /leP; lia)) => [N [? [? ?]]] ?.
have ? : Some ty == typing ctx (N @' tyl) by apply /typing_uappP; eexists; eassumption.
exists (N @' tyl) => /=.
split. constructor. by constructor.
split. done.
exists_matching_typing. apply /leP. unfoldN. by lia.

(*hf case*)
have : (eta_deficiency ctx M false = 0) \/ (eta_deficiency ctx M false = ((eta_deficiency ctx M false).-1).+1) by lia.
case => ?.
move => _. exists (M @' tyl) => /=.
split. by constructor.
split. done.
exists_matching_typing. apply /leP. unfoldN. by lia.

nat_norm. grab where typing. move /IH => /=. move /(_ ltac:(ssromega) ((eta_deficiency ctx M false).-1)).
case => _. move /(_ ltac:(assumption) ltac:(apply /leP; lia)) => [N [? [? ?]]] ?.
have ? : Some ty == typing ctx (N @' tyl) by apply /typing_uappP; eexists; eassumption.
exists (N @' tyl) => /=.
split. by constructor.
split. done.
exists_matching_typing. apply /leP. unfoldN. by lia.
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
Qed.


Lemma eta_expand_rec_2 : forall (w : nat) (M : term) (ctx : context typ) (ty : typ), Some ty == typing ctx M -> normal_form M ->
  exists N, normal_form N /\ (Some ty == typing ctx N) /\ eta_deficiency ctx N true <= eta_deficiency ctx M true - w.
Proof.
elim => /=.
intros. eexists. split. eassumption. split. eassumption. apply /leP. unfoldN. lia.
move => w IH M ctx *.
move : IH. move /(_ _ _ _ ltac:(eassumption) ltac:(eassumption)) => [N [? [?]]].

move Hn : (eta_deficiency ctx M true - w) => n.
case : n Hn => [|n] => ? ?.
eexists. split. eassumption. split. eassumption. apply /leP. unfoldN. lia.
grab where typing. case /(eta_expand_rec n). move /(_ ltac:(eassumption) ltac:(eassumption)).
move => [N' [? [? ?]]] _.
exists N'. split. done. split. done. apply /leP. unfoldN. lia.
Qed.

(*if there is a beta normal form derivation, then there is a beta normal eta long form derivation*)
Theorem eta_expand : forall (M : term) (ctx : context typ) (ty : typ), Some ty == typing ctx M -> normal_form M ->
  exists N, normal_form N /\ (Some ty == typing ctx N) /\ eta_deficiency ctx N true = 0.
Proof.
intros. grab where typing.
move /(eta_expand_rec_2 (eta_deficiency ctx M true)). move /(_ ltac:(assumption)) => [? [? [? ?]]]. 
eexists. split. eassumption. split. eassumption. unfoldN. lia.
Qed.

Lemma partial_chain_atom : forall a ts s, partial_chain s (atom a) ts <-> chain s a ts.
Proof.
move => a; elim.
intros *.
split; inversion; by constructor.

move => t ts IH s.
split.
inversion. apply : chain_cons.
eassumption. by rewrite <- IH.

inversion. apply : partial_chain_cons.
eassumption. by rewrite -> IH.
Qed.


Lemma head_form_atom_formula : forall M ctx t, head_form M -> normal_long_derivation ctx M t -> exists n, t = tyvar n.
Proof.
intros *. case.
move => ?. case => ? /= _. exists_matching_typing. clear. case : t => /=. 
by eauto.
1-2: by intros *; rewrite typ_size_pos_2 => ?; unfoldN; lia.

move => ? ? _ _. case => ? /= _. exists_matching_typing. clear. case : t => /=. 
by eauto.
1-2: by intros *; rewrite typ_size_pos_2 => ?; unfoldN; lia.

move => ? ? _. case => ? /= _. exists_matching_typing. clear. case : t => /=.
by eauto.
1-2: by intros *; rewrite typ_size_pos_2 => ?; unfoldN; lia.
Qed.


Lemma formula_to_typ_atom : forall labeling t n, well_formed_formula t -> formula_to_typ labeling 0 t = tyvar n -> exists a, t = atom a.
Proof.
move => ?. case => //.
intros *. inversion. lia.
by eauto.
Qed.


Lemma eta_true_false : forall M ctx, eta_deficiency ctx M true = 0 -> eta_deficiency ctx M false = 0.
Proof.
case => /=.

move => x ctx *. by case : (typing ctx x).

move => M N ctx. case : (typing ctx (M @ N)) => // *. unfoldN. by lia.

move => t M ctx. case : (typing ctx (abs t M)) => //.

move => M t ctx. case : (typing ctx (M @' t)) => // *. unfoldN. by lia.

move => M t. case : (typing t (uabs M)) => //.
Qed.


Lemma relax_depth_normal_derivation : forall (n m : nat) (Γ : list formula) (s : formula), 
  normal_derivation n Γ s -> (n <= m)%coq_nat -> normal_derivation m Γ s.
Proof.
elim /lt_wf_ind.
move => n IH. intros.
grab normal_derivation. inversion.

all: have : m = S (Nat.pred m) by lia.
all: move => ->.

constructor.
apply : IH; try eassumption; lia.

constructor.
move => a. grab where normal_derivation. move /(_ a) => ?.
apply : IH; try eassumption; lia.

apply : derive_atom; try eassumption.
apply : Forall_impl; last eassumption.
intros. apply : IH; try eassumption; lia.
Qed.


Lemma contains_wff : forall s t, contains s t -> well_formed_formula s -> well_formed_formula t.
Proof.
intros *. elim.
auto.

intros. grab well_formed_formula where quant. inversion.

intros. grab where well_formed_formula. apply.
grab lc. move /Lc.instantiate_pred. by apply. 
Qed.

Lemma partial_chain_wff : forall ts s t, well_formed_formula s -> partial_chain s t ts -> well_formed_formula t.
Proof.
elim.
intros. grab partial_chain. inversion.
apply : contains_wff; eassumption.

move => u ts IH.
intros. grab partial_chain. inversion.
apply : IH; last eassumption.
grab contains. move /contains_wff.
nip; first auto. by inversion.
Qed.

Lemma partial_chain_param_wff : forall ts s t u, well_formed_formula s -> partial_chain s t ts -> In u ts -> well_formed_formula u.
Proof.
elim.
intros. grab In. inversion.

move => t' ts IH.
intros. grab partial_chain. inversion.
grab In. case.

intro. subst.
grab contains. move /contains_wff.
nip; first auto. by inversion.

grab partial_chain.
move /IH. move => H' /H'. apply.
grab contains. move /contains_wff.
nip; first auto. by inversion.
Qed.

Definition big_sum (n : nat) : nat := nat_rect (fun _ => nat) 0 (fun i m => m + i.+1) n.

Lemma big_sum_zero : forall (n : nat), big_sum n = 0 -> n = 0.
Proof.
case => //=. move => n ?. unfoldN. by lia.
Qed.

Definition label_to_nat (a : label) : nat :=
  match a with
  | (x, y) => (big_sum (x+y)) + y
  end.

Definition next_label (a : label) : label :=
  match a with
  | (0, y) => (y.+1, 0)
  | (x.+1,y) => (x, y.+1)
  end.

Definition nat_to_label (n : nat) : label :=
  iter n next_label (0,0).


Lemma exists_bijective_labeling : exists (f : label -> nat), bijective f.
Proof.
exists label_to_nat, nat_to_label.
{
move => a.
move Hn : (label_to_nat a) => n.
elim : n a Hn.

move => [x y] /= ?.
have /big_sum_zero ? : big_sum (x + y) = 0 by unfoldN; lia.
unfoldN; f_equal; by lia.

move => n IH [x y] /=.
case : y => [| y] /=.
case : x => [| x] /=. done.
rewrite -/(_ + _). nat_norm. case.
have -> : big_sum x + x = label_to_nat (0,x) by reflexivity.
by move /IH => ->.

nat_norm.
have -> : big_sum (x + y).+1 + y = label_to_nat (x.+1, y) by done.
rewrite [label_to_nat] lock. case. unlock.
by move /IH => ->.
}
{
elim => //=.

move => n. move : (nat_to_label n) => [x y].
case : x => /=. 

rewrite -/(_ + _). nat_norm.
move => *. unfoldN. by lia.

move => m.
rewrite -/(_ + _). nat_norm => /=.
move => *. unfoldN. by lia.
}
Qed.


Lemma shift_labeling : forall (a : label) f, bijective f -> exists (f' : label -> nat), bijective f' /\ f' a = 0 /\ (forall b, f b < f a -> f' b = (f b).+1).
Proof.
move => a f /duplicate [/bij_inj ?] [g cfg cgf].

exists (fun (b : label) => if b == a then 0 else (if f b < f a then (f b).+1 else f b)).
split. exists (fun (n : nat) => if n == 0 then a else (if (n.-1) < f a then g (n.-1) else g n)).

move => b.
have := orbN (b == a). case /orP.
move /duplicate => [/eqP ? ->]. by subst.
move /duplicate => [/eqP ? /negbTE ->].

have := orbN (f b < f a). case /orP.
move /duplicate => [/leP ? H]. rewrite H => /=. rewrite H. by eauto.
move /duplicate => [/eqP ? /negbTE H]. rewrite H => /=.
move : H => /leP ?. have ? : f b <> f a by auto.
by do ? inspect_eqn.

move => n.
have := orbN (n == 0). case /orP.
move /duplicate => [/eqP ? ->] /=.
have : a == a by apply /eqP. move => ->. by subst.
move /duplicate => [/eqP ? /negbTE ->].

have := orbN (n.-1 < f a). case /orP.
move /duplicate => [/leP ? H]. rewrite H cgf H /=. 
have -> : (g n.-1 == a) = false.
apply /negP. move /eqP => ?. subst. move : H. rewrite cgf => ?. unfoldN. by lia.
unfoldN. by lia.

move /duplicate => [/eqP H' /negbTE H]. rewrite H.
have -> : (g n == a) = false.
apply /negP. move /eqP => ?. subst. move : H'. rewrite cgf => ?. unfoldN. by lia.
rewrite cgf. by inspect_eqn.

split. by have -> : a == a by apply /eqP.
move => b ?.
have := orbN (b == a). case /orP.
move /duplicate => [/eqP ? ->]. subst. unfoldN. by lia.
move /negbTE => ->. by inspect_eqn.
Qed.


Lemma formula_variable_bound : forall labeling t, exists (k : nat), forall labeling' n, 
  (forall (a : label), labeling a < k -> labeling a = labeling' a) -> formula_to_typ labeling n t = formula_to_typ labeling' n t.
Proof.
move => labeling. elim => /=.

move => ?. exists 0. by intros.

move => a. exists ((labeling a).+1). by move => ? ? /(_ a ltac:(done)) ->.

move => ? [k1 IH1] ? [k2 IH2]. exists (k1 + k2).
move => labeling' n H.
f_equal.
apply : IH1 => ? ?. apply : H. apply /leP. unfoldN. by lia.
apply : IH2 => ? ?. apply : H. apply /leP. unfoldN. by lia.

move => ? [k IH]. exists k. intros. f_equal. by apply IH.
Qed.


Lemma formula_variable_bound2 : forall (labeling : label -> nat), forall t, exists (k : nat), forall (a : label), k <= labeling a -> fresh_in a t.
Proof.
move => labeling. elim.

move => ?. exists 0. intros. by constructor.

move => b. exists ((labeling b).+1). move => a ?. constructor => ?. subst. unfoldN. by lia.

move => ? [k1 IH1] ? [k2 IH2]. exists (k1 + k2).
move => b ?. constructor.
apply : IH1. apply /leP. unfoldN. by lia.
apply : IH2. apply /leP. unfoldN. by lia.

move => ? [k IH]. exists k. intros. constructor. by apply IH.
Qed.


Lemma formulas_variable_bound2 : forall (labeling : label -> nat), forall ts, exists (k : nat), forall (a : label), k <= labeling a -> Forall (fresh_in a) ts.
Proof.
move => labeling. elim => /=.

by exists 0.

move => t ts [k1 IH].
have [k2 H] := @formula_variable_bound2 labeling t.
exists (k1 + k2). move => a ?. constructor.
apply : H. apply /leP. unfoldN. by lia.
apply : IH. apply /leP. unfoldN. by lia.
Qed.

Lemma shift_by_relabeling : forall labeling labeling' a, bijective labeling -> bijective labeling' -> labeling' a = 0 -> 
  (forall b : label, labeling b < labeling a -> labeling' b = (labeling b).+1) ->
  forall t n, (forall b : label, labeling a <= labeling b -> fresh_in b t) -> formula_to_typ labeling n.+1 t = formula_to_typ labeling' n (instantiate (Formula.atom a) n t).
Proof.
move => labeling  labeling' a lbi l'bi l'a ll'. elim => /=.

move => x n _.
have : (n = x) \/ (x <> n)%coq_nat by lia. case => ?.
subst. inspect_eqb => /=. rewrite l'a. by nat_norm.
by inspect_eqb.

move => b n llf.
move : (ll' b). apply : unnest.
apply /leP. suff : ~(labeling a <= labeling b)%coq_nat by intro; lia.
move => H. move : llf. move /(_ b ltac:(apply /leP; eassumption)). by inversion.

move => ->. by nat_norm.

move => ? IH1 ? IH2 n llf. f_equal.
apply : IH1 => b. move /llf. by inversion.
apply : IH2 => b. move /llf. by inversion.

move => ? IH n llf. f_equal.
apply : IH => b. move /llf. by inversion.
Qed.


(*the usual presentation of intro_quant*)
Lemma normal_intro_quant_fresh : forall (s: formula) (Γ : list formula) (a : label) (n : nat), 
  Forall (fresh_in a) Γ -> fresh_in a s ->
  normal_derivation n Γ (instantiate (atom a) 0 s) -> normal_derivation (S n) Γ (Formula.quant s).
Proof.
move => s Γ a n H *.
constructor => b.
grab normal_derivation. move /(substitute_normal_derivation a b).
rewrite rename_instantiation; first last. done.
rewrite <- map_substitute_fresh_label.
apply. done.
Qed.


(*if there is a derivation, then there is a iipc2 eta-long beta-normal derivation*)
Theorem f_to_normal_derivation : forall M labeling t Gamma, bijective labeling ->
  let ctx := (map (fun t => Some (formula_to_typ labeling 0 t)) Gamma) in normal_long_derivation ctx M (formula_to_typ labeling 0 t) ->
  well_formed_formula t -> Forall well_formed_formula Gamma -> exists d, normal_derivation d Gamma t.
Proof.
elim /(f_ind term_size).
move => ? IH labeling t Gamma lbi ctx *.
grab normal_long_derivation. case => *.
grab normal_form. inversion.

(*head form case*)
{
grab head_form => Hhf. move : (Hhf) => /head_form_atom_formula. 
move /(_ _ _ ltac:(constructor; try by [eassumption | constructor])) => [? ?].

move : (Hhf) => /f_hf_to_partial_chain. 
move /(_ _ ltac:(eassumption) _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
apply : unnest. by apply : eta_true_false.
grab where formula_to_typ. move /formula_to_typ_atom. move /(_ ltac:(assumption)) => [a ?]. subst.
move => [s [ts] [? [/duplicate [/partial_chain_param_wff wff_ts /partial_chain_atom ?] ?]]].

(*each argument is derivable*)
have : exists d, Forall (normal_derivation d Gamma) ts.
apply : Forall_exists_monotone. intros. apply : relax_depth_normal_derivation; eassumption.
grab In. move /Forall_In. move /(_ _ ltac:(eassumption)). move /wff_ts.
move /Forall_In_iff. move /Forall_and. move /(_ _ ltac:(eassumption)).
apply /Forall_impl.
move => ? [? [? [?]]] /IH. apply; try eassumption.
unfoldN. by lia.

move => [d ?]. exists (d.+1). apply : derive_atom; try eassumption.
}

(*abs normal form case*)
{
grab where eta_deficiency => /=. exists_matching_typing => ?.
grab where typing. move /typing_absP => [?] ?. move /nld_intro. move /(_ ltac:(assumption) ltac:(assumption)).
revert dependent t. case => //= s t ?. case => ? ?. subst.
grab well_formed_formula. inversion.
have -> : (Some (formula_to_typ labeling 0 s) :: ctx) = [seq Some (formula_to_typ labeling 0 t) | t <- (s :: Gamma)] by reflexivity.
move /IH => /=. move /(_ ltac:(ssromega) ltac:(assumption) ltac:(assumption) ltac:(by apply /Forall_cons_iff)).
move => [? ?]. eexists. apply : derive_arr; eassumption.
}

(*uabs normal form case*)
{
grab where eta_deficiency => /=. exists_matching_typing => ?.
grab where typing. move /typing_uabsP => [?] ?. 
revert dependent t. case => //= t ?. case => ?. subst.
grab well_formed_formula. inversion.

have [k Hk] := @formulas_variable_bound2 labeling (t :: Gamma).
case : (lbi) => g cll cgl.
pose a := g k.
move : (Hk a). rewrite /a cgl. move /(_ ltac:(done)). inversion.

have := @shift_labeling a labeling ltac:(assumption). move => [labeling' [? [Hl'2 ?]]].
have shift := @shift_by_relabeling labeling labeling' a ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption).
rewrite shift; first last.
move => b. rewrite /a cgl. move /Hk. by inversion.

grab where eta_deficiency.
have -> : ctxmap (shift_typ 1 0) ctx = [seq Some (formula_to_typ labeling' 0 t) | t <- Gamma].
{
subst ctx. clear IH.
revert dependent Gamma. elim => //=.
move => s Gamma IH. inversion. move => Hk. inversion. f_equal.
have := @Lc.instantiate_eq0 (atom a) s 0 ltac:(assumption).
rewrite shift_formula_to_typ => //.
move => {2}<-. nat_norm.
f_equal. apply : shift.
move => b. rewrite /a cgl. move /Hk. inversion. grab Forall. by inversion.

apply : IH => //.
move => b /Hk. inversion. grab Forall. inversion. by constructor.
}

move => ? /nld_intro. move /(_ ltac:(assumption) ltac:(assumption)).
move /IH => /=. move /(_ ltac:(unfoldN; lia) ltac:(assumption) _ ltac:(assumption)).
apply : unnest. apply : Lc.instantiate_pred. by nat_norm. by constructor.
move => [d] /normal_intro_quant_fresh nd.

exists (d.+1). by apply : nd.
}
Qed.





Theorem subject_reduction ctx t t' ty :
  t ->r t' -> ctx \|- t \: ty -> ctx \|- t' \: ty.
Proof.
elim => //.
move => ? ? ? ? ? H.
move /subject_reduction_proof.subject_reduction. 
by auto.
Qed.


Theorem iipc2_to_normal_derivation : forall (Gamma: list formula) (t: formula), iipc2 Gamma t -> exists d, normal_derivation d Gamma t.
Proof.
intros *. have [labeling ?] := @exists_bijective_labeling.
move /duplicate => [/iipc2_wff [? ?]].
move /iipc2_to_f. move /(_ labeling ltac:(apply /bij_inj => //)) => [?].
case /duplicate. move /strong_normalization_proof_typefree.typed_term_is_snorm.
move /sn_to_not_reducible => [N [?]].
apply : swap. move /subject_reduction. move /(_ _ ltac:(eassumption)) => D.
move /not_reducible_to_nf. move /(_ _ _ D).
move : D => /eta_expand. move => H {}/H => [[N' [? [? ?]]]].
grab where typing. move /nld_intro. move /(_ ltac:(assumption) ltac:(assumption)) => ?.
apply : f_to_normal_derivation; try eassumption.
Qed.



Section derivation_to_iipc2.

Import InstantiateAll.
Import DerivationIffDerivationDepth.

Theorem derivation_to_iipc2 : forall (Gamma: list formula) (t: formula), derivation Gamma t -> Forall well_formed_formula Gamma -> well_formed_formula t -> iipc2 Gamma t.
Proof.
move => Gamma t.
move /derivation_exists_depth. case => d. elim : d Gamma t.

intros *. inversion => *. by apply : iipc2_ax.

move => d IH Gamma t. inversion.

move => *. by apply : iipc2_ax.

move => *. grab derivation_depth => /instantiate_all_derivation_depth. grab derivation_depth => /instantiate_all_derivation_depth.
move => /=. rewrite (@lc_instantiate_all t) //. rewrite (lc_map_instantiate_all) //. 
move /IH. move /(_ ltac:(assumption)). 
match goal with |- context[instantiate_all 0 ?s] => pose s' := (instantiate_all 0 s) end.
have ? : well_formed_formula s' by apply : instantiate_all_lc.
move /(_ ltac:(by constructor)) => *.
apply : iipc2_elim_arr; by eauto.

move => ?. inversion. apply : iipc2_intro_arr. apply : IH => //. by constructor.

move => ? /Lc.succ_instantiate. move /(_ ltac:(assumption)) => /= ?.
apply : iipc2_elim_quant => //. apply : IH; by [| constructor].

move => ?. inversion.
have [a /Forall_cons_iff [? ?]] := exists_fresh (s :: Gamma).
rewrite -[s in quant s](@bind_instantiate a _ 0) //.
apply : iipc2_intro_quant => //.
apply : IH => //.
apply : Lc.instantiate_pred; by [| constructor].
Qed.

End derivation_to_iipc2.


