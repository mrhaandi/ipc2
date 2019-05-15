Require Import Utf8.
Require Import List.
Import ListNotations.
Require Import Omega.

From Coq Require Import ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Maximal Implicit Insertion.

Require Import FormulaFacts.
Require Import Derivations.
Require Import DerivationsFacts.
Require Import Encoding.
Require Import UserTactics.
Require Import Psatz. (*lia : linear integer arithmetic*)
Require Import Diophantine.

Require Import ListFacts.

Lemma derive_quantified_arrow : forall n s t, derivation [triangle] (quantify_formula n t) -> derivation [triangle] (quantify_formula n (arr s t)).
Proof.
elim.
intros.
apply intro_arr.
apply : weakening; [eassumption | list_inclusion].
intros.
simpl.
apply intro_quant.

move => a.
grab derivation.
simpl.
move /elim_quant => /(_ (instantiate (atom a) 0 (quantify_formula n t))).
apply : unnest. apply : contains_trans; first last; by constructor.

rewrite ? instantiate_quantification.
(have -> : (n + 0) = n by omega) => /=.
by auto.
Qed.


Lemma eliminate_I : forall (ds : list diophantine) (s : formula), In s (ΓI ds) -> derivation [triangle] s.
Proof.
intros.
filter_context_derivation.
unfold s_x_d.
apply : derive_quantified_arrow.
move : (diophantine_variable_bound ds).
elim ds.
(*base case ds = []*)
elim.
derivation_rule.
simpl; intros.
apply : intro_quant.
intros.
rewrite instantiate_quantification.
assumption.

(*inductive case*)
case; (intros; simpl; do ? (apply : derive_quantified_arrow); auto).
Qed.


(*replace ΓS by a_s in assumption*)
Ltac generalize_ΓS :=
  match goal with
  | [ H' : ∀ s : formula, In s ?ΓS → encodes_sum s, H : derivation ?Γ ?s |- _] => 
    match Γ with
    | context G [ΓS] => let G' := context G [[a_s]] in 
      eapply (context_generalization (Δ := G')) in H;
      last (
        let H_in := fresh in intros ? H_in; filter_context_derivation;
        move /H' : H_in => [? [? [? [? _]]]]; subst; derivation_rule)
    end
  end.

(*replace ΓP by a_p in assumption*)
Ltac generalize_ΓP :=
  match goal with
  | [ H' : ∀ s : formula, In s ?ΓP → encodes_prod s, H : derivation ?Γ ?s |- _] => 
    match Γ with
    | context G [ΓP] => let G' := context G [[a_p]] in 
      eapply (context_generalization (Δ := G')) in H;
      last (
        let H_in := fresh in intros ? H_in; filter_context_derivation;
        move /H' : H_in => [? [? [? [? _]]]]; subst; derivation_rule)
    end
  end.

(*replace ΓU by a_u in assumption*)
Ltac generalize_ΓU :=
  match goal with
  | [ H' : ∀ s : formula, In s ?ΓU → represents_nat s, H : derivation ?Γ ?s |- _] => 
    match Γ with
    | context G [ΓU] => let G' := context G [[a_u]] in 
      eapply (context_generalization (Δ := G')) in H;
      last (
        let H_in := fresh in intros ? H_in; filter_context_derivation;
        move /H' : H_in => [? [? ?]]; subst; derivation_rule)
    end
  end.

(*replace ΓI by triangle in assumption*)
Ltac generalize_ΓI :=
  match goal with
  | [ H : derivation ?Γ _ |- _] => 
    match Γ with
    | context G [ΓI] => let G' := context G [[triangle]] in 
      eapply (context_generalization (Δ := G')) in H;
      last (
        intros ? ?; filter_context_derivation)
    end
  end.


Ltac decompose_derivation := 
  match goal with
  | [H : derivation _ ?s |- _] => 
    match eval hnf in s with
    | arr _ _ => (move /inv_arr : H; apply : unnest; [| apply : unnest]); first last; first move => H
    | atom _ => 
      let s := fresh in 
      let H' := fresh in
      move /inv_atom : H; apply : unnest; first last; first move => [s [? [H' [? ?]]]]
    end
  end.

Lemma wff_arr : forall s t, well_formed_formula s -> well_formed_formula t -> well_formed_formula (arr s t).
Proof. intros. by constructor. Qed.

Lemma wff_GammaU : forall Gamma, (forall (s : formula), In s Gamma → represents_nat s) -> Forall well_formed_formula Gamma.
Proof.
move => ?. move /Forall_In_iff.
apply /Forall_impl. clear. move => s.
move => [? [? ?]]. subst.
by do ? constructor.
Qed.

Lemma wff_GammaS : forall Gamma, (forall (s : formula), In s Gamma → encodes_sum s) -> Forall well_formed_formula Gamma.
Proof.
move => ?. move /Forall_In_iff.
apply /Forall_impl. clear. move => s.
firstorder subst.
by do ? constructor.
Qed.

Lemma wff_GammaP : forall Gamma, (forall (s : formula), In s Gamma → encodes_prod s) -> Forall well_formed_formula Gamma.
Proof.
move => ?. move /Forall_In_iff.
apply /Forall_impl. clear. move => s.
firstorder subst.
by do ? constructor.
Qed.

Lemma wff_U : forall s, well_formed_formula (U s) -> well_formed_formula s.
Proof.
move => ?. inversion.
by do 3 (grab lc; inversion).
Qed.

Lemma wff_S1 : forall s1 s2 s3, well_formed_formula (S s1 s2 s3) -> well_formed_formula s1.
Proof. move => s1 ? ?. inversion. by do 2 (grab lc where s1; inversion). Qed.

Lemma wff_S2 : forall s1 s2 s3, well_formed_formula (S s1 s2 s3) -> well_formed_formula s2.
Proof. move => ? s2 ?. inversion. by do 3 (grab lc where s2; inversion). Qed.

Lemma wff_S3 : forall s1 s2 s3, well_formed_formula (S s1 s2 s3) -> well_formed_formula s3.
Proof. move => ? ? s3. inversion. by do 4 (grab lc where s3; inversion). Qed.

Lemma wff_P1 : forall s1 s2 s3, well_formed_formula (P s1 s2 s3) -> well_formed_formula s1.
Proof. move => s1 ? ?. inversion. by do 2 (grab lc where s1; inversion). Qed.

Lemma wff_P2 : forall s1 s2 s3, well_formed_formula (P s1 s2 s3) -> well_formed_formula s2.
Proof. move => ? s2 ?. inversion. by do 3 (grab lc where s2; inversion). Qed.

Lemma wff_P3 : forall s1 s2 s3, well_formed_formula (P s1 s2 s3) -> well_formed_formula s3.
Proof. move => ? ? s3. inversion. by do 4 (grab lc where s3; inversion). Qed.

Lemma wff_InGammaS1 : forall s1 s2 s3 Gamma, (forall (s : formula), In s Gamma → encodes_sum s) -> In (S s1 s2 s3) Gamma -> well_formed_formula s1.
Proof. move => ? ? ? ? H /H. firstorder subst. grab @eq. inversion. by do ? constructor. Qed.

Lemma wff_InGammaS2 : forall s1 s2 s3 Gamma, (forall (s : formula), In s Gamma → encodes_sum s) -> In (S s1 s2 s3) Gamma -> well_formed_formula s2.
Proof. move => ? ? ? ? H /H. firstorder subst. grab @eq. inversion. by do ? constructor. Qed.

Lemma wff_InGammaS3 : forall s1 s2 s3 Gamma, (forall (s : formula), In s Gamma → encodes_sum s) -> In (S s1 s2 s3) Gamma -> well_formed_formula s3.
Proof. move => ? ? ? ? H /H. firstorder subst. grab @eq. inversion. by do ? constructor. Qed.

Lemma wff_InGammaP1 : forall s1 s2 s3 Gamma, (forall (s : formula), In s Gamma → encodes_prod s) -> In (P s1 s2 s3) Gamma -> well_formed_formula s1.
Proof. move => ? ? ? ? H /H. firstorder subst. grab @eq. inversion. by do ? constructor. Qed.

Lemma wff_InGammaP2 : forall s1 s2 s3 Gamma, (forall (s : formula), In s Gamma → encodes_prod s) -> In (P s1 s2 s3) Gamma -> well_formed_formula s2.
Proof. move => ? ? ? ? H /H. firstorder subst. grab @eq. inversion. by do ? constructor. Qed.

Lemma wff_InGammaP3 : forall s1 s2 s3 Gamma, (forall (s : formula), In s Gamma → encodes_prod s) -> In (P s1 s2 s3) Gamma -> well_formed_formula s3.
Proof. move => ? ? ? ? H /H. firstorder subst. grab @eq. inversion. by do ? constructor. Qed.

Ltac inspect_wff :=
  do ? (
    lazymatch goal with
    | [H : well_formed_formula (U ?s) |- well_formed_formula ?s] => by apply : (wff_U H)
    | [H : well_formed_formula (S ?s _ _) |- well_formed_formula ?s] => by apply : (wff_S1 H)
    | [H : well_formed_formula (S _ ?s _) |- well_formed_formula ?s] => by apply : (wff_S2 H)
    | [H : well_formed_formula (S _ _ ?s) |- well_formed_formula ?s] => by apply : (wff_S3 H)
    | [H : well_formed_formula (P ?s _ _) |- well_formed_formula ?s] => by apply : (wff_P1 H)
    | [H : well_formed_formula (P _ ?s _) |- well_formed_formula ?s] => by apply : (wff_P2 H)
    | [H : well_formed_formula (P _ _ ?s) |- well_formed_formula ?s] => by apply : (wff_P3 H)
    | [H1 : forall (s : formula), In s ?Gamma → encodes_sum s, H2 : In (S ?s _ _) ?Gamma |- well_formed_formula ?s] => by apply : (wff_InGammaS1 H1 H2)
    | [H1 : forall (s : formula), In s ?Gamma → encodes_sum s, H2 : In (S _ ?s _) ?Gamma |- well_formed_formula ?s] => by apply : (wff_InGammaS2 H1 H2)
    | [H1 : forall (s : formula), In s ?Gamma → encodes_sum s, H2 : In (S _ _ ?s) ?Gamma |- well_formed_formula ?s] => by apply : (wff_InGammaS3 H1 H2)
    | [H1 : forall (s : formula), In s ?Gamma → encodes_prod s, H2 : In (P ?s _ _) ?Gamma |- well_formed_formula ?s] => by apply : (wff_InGammaP1 H1 H2)
    | [H1 : forall (s : formula), In s ?Gamma → encodes_prod s, H2 : In (P _ ?s _) ?Gamma |- well_formed_formula ?s] => by apply : (wff_InGammaP2 H1 H2)
    | [H1 : forall (s : formula), In s ?Gamma → encodes_prod s, H2 : In (P _ _ ?s) ?Gamma |- well_formed_formula ?s] => by apply : (wff_InGammaP3 H1 H2)
    | [|- Forall well_formed_formula (ΓI _)] => by apply ΓI_ds_wff
    | [|- Forall well_formed_formula calC] => by apply calC_wff
    | [|- Forall well_formed_formula []] => constructor
    | [|- Forall well_formed_formula (_ :: _)] => constructor
    | [|- Forall well_formed_formula (_ ++ _)] => apply /Forall_app_iff; split
    | [_ :  forall (s : formula), In s ?Gamma → represents_nat s |- Forall well_formed_formula ?Gamma] => by apply : wff_GammaU
    | [_ :  forall (s : formula), In s ?Gamma → encodes_sum s |- Forall well_formed_formula ?Gamma] => by apply : wff_GammaS
    | [_ :  forall (s : formula), In s ?Gamma → encodes_prod s |- Forall well_formed_formula ?Gamma] => by apply : wff_GammaP
    | [|- well_formed_formula ?s] => 
      match eval hnf in s with
      | (arr _ _) => apply : wff_arr
      | (atom _) => by constructor
      end
    end).


Lemma get_interpretation : forall (s : formula) (ΓU : list formula),
  (forall {s : formula}, In s ΓU -> represents_nat s) ->
  well_formed_formula (U s) ->
  derivation (ΓU ++ [triangle; a_s; a_p]) (U s) ->
  exists (m : nat), interpretation s m /\ m > 0.
Proof.
move => s ΓU HΓU ? ?.
decompose_derivation. decompose_derivation. decompose_derivation.
filter_context_chain => ?.
match goal with [ _ : In ?s ΓU |- _] => have : represents_nat s by auto end.
move => [m [? ?]]; subst.
exists m; split; last done.
decompose_chain.
decompose_Forall.
do 2 generalize_ΓU.
decompose_derivation. decompose_derivation. decompose_derivation. decompose_derivation.
do 2 filter_context_chain.
decompose_Forall.
grab derivation; grab derivation => HD2 HD1.
constructor. by inspect_wff.
(*show +s -> +m*)
do 2 (apply intro_arr).
eapply (context_generalization (Δ := (represent_nat m :: to_dagger s :: calC))) in HD1.
2 : { intros; filter_context_derivation. }
have : derivation (represent_nat m :: to_dagger s :: calC) (to_dagger s) by derivation_rule.
intros; by derivation_rule.
(*show +m -> +s*)
eapply (context_generalization (Δ := ((to_dagger (represent_nat m)) :: calC))) in HD2.
2 : { intros; filter_context_derivation. }
derivation_rule.
all: by inspect_wff.
Qed.


Lemma chain_represents_nat : forall s params a, chain s a params -> represents_nat s -> a = get_label a_u.
Proof.
intros * => ? [? [? ?]]. subst. by decompose_chain.
Qed.

(*cannt show well-formedness
Lemma get_normal_interpretation : forall (n: nat) (s : formula) (ΓU : list formula),
  (forall {s : formula}, In s ΓU -> represents_nat s) ->
  normal_derivation n (ΓU ++ [triangle; a_s; a_p]) (U s) ->
  exists (m : nat), interpretation s m /\ m > 0.
Proof.
move => n s ΓU HΓU ?.
decompose_normal_derivation.
filter_context_chain => ?.
match goal with [ _ : In ?s ΓU |- _] => have : represents_nat s by auto end.
move => [m [? ?]]; subst.
exists m; split; last done.
decompose_chain.
decompose_Forall.
decompose_normal_derivation.
do 2 filter_context_chain.
decompose_Forall.
grab derivation; grab derivation => HD2 HD1.
constructor. by inspect_wff.
(*show +s -> +m*)
do 2 (apply intro_arr).
eapply (context_generalization (Δ := (represent_nat m :: to_dagger s :: calC))) in HD1.
2 : { intros; filter_context_derivation. }
have : derivation (represent_nat m :: to_dagger s :: calC) (to_dagger s) by derivation_rule.
intros; by derivation_rule.
(*show +m -> +s*)
eapply (context_generalization (Δ := ((to_dagger (represent_nat m)) :: calC))) in HD2.
2 : { intros; filter_context_derivation. }
derivation_rule.
all: by inspect_wff.


all: move /chain_represents_nat; by move /(_ ltac:(auto)).
Qed.
*)





Lemma derivation_atom_eq : forall (a b : label), ~(In (Formula.atom a) (dagger :: calC)) -> ~(In (Formula.atom b) (dagger :: calC)) -> 
  derivation calC (Formula.arr (to_dagger (Formula.atom a)) (to_dagger (Formula.atom b))) -> a = b.
Proof.
intros.
decompose_derivation.
decompose_derivation.
decompose_derivation.
filter_context_chain. exfalso; intuition.
decompose_Forall.
decompose_derivation.
filter_context_chain; try (firstorder done).
all: by inspect_wff.
Qed.

Lemma chain_intro_sum (params : list formula) : chain s_x_s (get_label triangle) params -> 
  exists (s1 s2 s3 s4 s5 : formula), 
    (params = [U s1; U s2; U s3; U s4; U s5; S s1 s2 s3; S s2 one s4; S s3 one s5; Formula.arr (S s1 s4 s5) triangle]) /\ Forall well_formed_formula params.
Proof.
case; intros; first do ? decompose_contains.
grab chain; do ? decompose_contains.
move => ?; decompose_chain.
do 5 eexists.
split => //=.
rewrite ? Lc.instantiate_eq0 //.
do ? constructor; assumption.
Qed.

Lemma chain_intro_prod (params : list formula) : chain s_x_p (get_label triangle) params -> 
  exists (s1 s2 s3 s4 s5 : formula), 
    (params = [U s1; U s2; U s3; U s4; U s5; P s1 s2 s3; S s2 one s4; S s3 s1 s5; Formula.arr (P s1 s4 s5) triangle]) /\ Forall well_formed_formula params.
Proof.
case; intros; first do ? decompose_contains.
grab chain; do ? decompose_contains.
move => ?; decompose_chain.
do 5 eexists.
split => //=.
rewrite ? Lc.instantiate_eq0 //.
do ? constructor; assumption.
Qed.


Lemma chain_intro_element (params : list formula): chain s_x_u (get_label triangle) params -> 
  exists (s : formula), lc 0 s /\
    (params = [U s; quant ( arr (U (var 0)) (arr (S s one (var 0)) (arr (P (var 0) one (var 0)) triangle)))]) /\ Forall well_formed_formula params.
Proof.
case; intros; first do ? decompose_contains.
grab chain; do ? decompose_contains.
move => ?; decompose_chain.
eexists. split; [eassumption | ].
split => //=.
grab lc. move /duplicate => [? /Lc.relax]. move /(_ 1 ltac:(auto)) => ?.
by (do ? constructor).
Qed.

(*
Lemma chain_intro_sum (params : list formula) : chain s_x_s (get_label triangle) params -> 
  exists (s1 s2 s3 s4 s5 : formula), 
    (params = [U s1; U s2; U s3; U s4; U s5; S s1 s2 s3; S s2 one s4; S s3 one s5; Formula.arr (S s1 s4 s5) triangle]).
Proof.
case; intros; first do ? decompose_contains.
grab chain; do ? decompose_contains.
move => ?; decompose_chain.
by do 5 eexists.
Qed.


Lemma chain_intro_prod (params : list formula) : chain s_x_p (get_label triangle) params -> 
  exists (s1 s2 s3 s4 s5 : formula), 
    (params = [U s1; U s2; U s3; U s4; U s5; P s1 s2 s3; S s2 one s4; S s3 s1 s5; Formula.arr (P s1 s4 s5) triangle]).
Proof.
case; intros; first do ? decompose_contains.
grab chain; do ? decompose_contains.
move => ?; decompose_chain.
by do 5 eexists.
Qed.


Lemma chain_intro_element (params : list formula): chain s_x_u (get_label triangle) params -> 
  exists (s : formula), lc 0 s /\
    (params = [U s; quant ( arr (U (var 0)) (arr (S s one (var 0)) (arr (P (var 0) one (var 0)) triangle)))]).
Proof.
case; intros; first do ? decompose_contains.
grab chain; do ? decompose_contains.
move => ?; decompose_chain.
eexists. by split; [eassumption | ].
Qed.
*)

Lemma derivation_arr_trans : forall (Γ : list formula) (s t u : formula),
  derivation Γ (arr s t) -> derivation Γ (arr t u) -> derivation Γ (arr s u).
Proof.
intros * => Hst Htu.
apply intro_arr.
apply (weakening (Δ := (s :: Γ))) in Hst; last list_inclusion.
apply (weakening (Δ := (s :: Γ))) in Htu; last list_inclusion.
move : Htu => /elim_arr. apply.
move : Hst => /elim_arr. apply.
apply : ax. by constructor.
Qed.


Lemma interpretation_soundness : forall (s : formula) (m1 m2 : nat), interpretation s m1 -> interpretation s m2 -> m1 = m2.
Proof.
intros s m1 m2.
inversion. inversion.
have Hm1m2 : derivation calC (arr (to_dagger (represent_nat m1)) (to_dagger (represent_nat m2))).
apply: intro_arr.
set t := to_dagger (represent_nat m2).
set u := to_dagger (represent_nat m1).
set s' := (to_dagger s).
have Hu : derivation (u :: calC) u by derivation_rule.
have Hus' : derivation (u :: calC) (arr u s').
apply: (weakening (Γ := calC)) => //. intuition.
have Hs't : derivation (u :: calC) (arr s' t).
apply: (weakening (Γ := calC)) => //. intuition.
have Hs' : derivation (u :: calC) s' by derivation_rule.
by derivation_rule.
suff : (1, m1) = (1, m2) by case.
apply: derivation_atom_eq Hm1m2; firstorder done.
Qed.


Lemma interpretation_soundness_arr : forall (s1 s2 : formula) (m1 m2 : nat),
  derivation calC (arr (to_dagger s1) (to_dagger s2)) -> interpretation s1 m1 -> interpretation s2 m2 -> m1 = m2.
Proof.
intros * => ?. inversion. inversion.
have ? : derivation calC (arr (to_dagger (represent_nat m1)) (to_dagger s2))
by apply: derivation_arr_trans; eassumption.

have ? : derivation calC (arr (to_dagger (represent_nat m1)) (to_dagger (represent_nat m2)))
by apply: derivation_arr_trans; eassumption.

suff : get_label (represent_nat m1) = get_label (represent_nat m2) by case.
apply: derivation_atom_eq => //; firstorder done.
Qed.



Lemma assert_sum : forall (s1 s2 s3 : formula) (m1 m2 m3 : nat) (ΓS : list formula),
  (forall {s : formula}, In s ΓS -> encodes_sum s) ->
  interpretation s1 m1 -> interpretation s2 m2 -> interpretation s3 m3 -> 
  well_formed_formula (S s1 s2 s3) ->
  derivation (ΓS ++ [triangle; a_u; a_p]) (S s1 s2 s3) ->
  m1 + m2 = m3.
Proof.
intros * => ? Hs1 Hs2 Hs3 ? HD.
decompose_derivation. decompose_derivation. decompose_derivation. decompose_derivation.
filter_context_chain => Hc.
match goal with [ _ : In ?s ΓS |- _] => have : encodes_sum s by auto end.
move => [s1' [s2' [s3' [?]]]].
subst; decompose_chain.
decompose_Forall.
do ? (generalize_ΓS).

decompose_derivation. decompose_derivation. decompose_derivation. decompose_derivation. decompose_derivation. decompose_derivation.
do ? (filter_context_chain).
decompose_Forall.
have Hs1s1' : derivation calC (arr (to_dagger s1') (to_dagger s1)).
apply intro_arr.
apply: (context_generalization); [eassumption | by intros; filter_context_derivation].

have Hs2s2' : derivation calC (arr (to_dagger s2') (to_dagger s2)).
apply intro_arr. 
apply: (context_generalization); [eassumption | by intros; filter_context_derivation].

have Hs3s3' : derivation calC (arr (to_dagger s3') (to_dagger s3)).
apply intro_arr. 
apply: (context_generalization); [eassumption | by intros; filter_context_derivation].

move => [m1' [m2' [m3' [Hs1' [Hs2' [Hs3' ?]]]]]].

have ? : m1' = m1 by apply: (interpretation_soundness_arr Hs1s1'); assumption.
have ? : m2' = m2 by apply: (interpretation_soundness_arr Hs2s2'); assumption.
have ? : m3' = m3 by apply: (interpretation_soundness_arr Hs3s3'); assumption.
by subst.
all: inspect_wff.
Qed.


Lemma assert_prod : forall (s1 s2 s3 : formula) (m1 m2 m3 : nat) (ΓP : list formula),
  (forall {s : formula}, In s ΓP -> encodes_prod s) ->
  interpretation s1 m1 -> interpretation s2 m2 -> interpretation s3 m3 -> 
  well_formed_formula (P s1 s2 s3) ->
  derivation (ΓP ++ [triangle; a_u; a_s]) (P s1 s2 s3) ->
  m1 * m2 = m3.
Proof.
intros * => ? Hs1 Hs2 Hs3 ? HD.
decompose_derivation. decompose_derivation. decompose_derivation. decompose_derivation.
filter_context_chain => Hc.
match goal with [ _ : In ?s ΓP |- _] => have : encodes_prod s by auto end.
move => [s1' [s2' [s3' [?]]]].
subst.
decompose_chain.
decompose_Forall.
do ? (generalize_ΓP).

decompose_derivation. decompose_derivation. decompose_derivation. decompose_derivation. decompose_derivation. decompose_derivation.
do ? (filter_context_chain).
decompose_Forall.
have Hs1s1' : derivation calC (arr (to_dagger s1') (to_dagger s1)).
apply intro_arr.
apply: (context_generalization); [eassumption | by intros; filter_context_derivation].

have Hs2s2' : derivation calC (arr (to_dagger s2') (to_dagger s2)).
apply intro_arr. 
apply: (context_generalization); [eassumption | by intros; filter_context_derivation].

have Hs3s3' : derivation calC (arr (to_dagger s3') (to_dagger s3)).
apply intro_arr. 
apply: (context_generalization); [eassumption | by intros; filter_context_derivation].

move => [m1' [m2' [m3' [Hs1' [Hs2' [Hs3' ?]]]]]].

have ? : m1' = m1 by apply: (interpretation_soundness_arr Hs1s1'); assumption.
have ? : m2' = m2 by apply: (interpretation_soundness_arr Hs2s2'); assumption.
have ? : m3' = m3 by apply: (interpretation_soundness_arr Hs3s3'); assumption.
by subst.
all: inspect_wff.
Qed.


Lemma generalize_ISP : forall (n : nat) (ΓU ΓS ΓP : list formula), 
  (forall {s : formula}, In s ΓS -> encodes_sum s) ->
  (forall {s : formula}, In s ΓP -> encodes_prod s) ->
  forall (ds : list diophantine) (s : formula), normal_derivation n (ΓI ds ++ ΓU ++ ΓS ++ ΓP) (U s) -> derivation (ΓU ++ [triangle; a_s; a_p]) (U s).
Proof.
intros.
grab normal_derivation. move /normal_derivation_soundness => HD.
apply : (context_generalization HD).
intros.
filter_context_derivation.
apply : (weakening (Γ := [triangle])); last by list_inclusion.
apply : (eliminate_I (ds := ds)); list_inclusion.
match goal with | [ _ : In ?s ΓS |- _] => have : encodes_sum s by auto end.
move => [? [? [? [? ?]]]]; subst; derivation_rule.
match goal with | [ _ : In ?s ΓP |- _] => have : encodes_prod s by auto end.
move => [? [? [? [? ?]]]]; subst; derivation_rule.
Qed.


Lemma generalize_IUP : forall (n : nat) (ΓU ΓS ΓP : list formula), 
  (forall {s : formula}, In s ΓU -> represents_nat s) ->
  (forall {s : formula}, In s ΓP -> encodes_prod s) ->
  forall (ds : list diophantine) (s1 s2 s3 : formula), normal_derivation n (ΓI ds ++ ΓU ++ ΓS ++ ΓP) (S s1 s2 s3) -> 
  derivation (ΓS ++ [triangle; a_u; a_p]) (S s1 s2 s3).
Proof.
intros.
grab normal_derivation. move /normal_derivation_soundness => HD.
apply : (context_generalization HD).
intros.
filter_context_derivation.
apply : (weakening (Γ := [triangle])); last by list_inclusion.
apply : (eliminate_I (ds := ds)); list_inclusion.
match goal with | [ _ : In ?s ΓU |- _] => have : represents_nat s by auto end.
move => [? [? ?]]; subst; derivation_rule.
match goal with | [ _ : In ?s ΓP |- _] => have : encodes_prod s by auto end.
move => [? [? [? [? ?]]]]; subst; derivation_rule.
Qed.


Lemma generalize_IUS : forall (n : nat) (ΓU ΓS ΓP : list formula), 
  (forall {s : formula}, In s ΓU -> represents_nat s) ->
  (forall {s : formula}, In s ΓS -> encodes_sum s) ->
  forall (ds : list diophantine) (s1 s2 s3 : formula), normal_derivation n (ΓI ds ++ ΓU ++ ΓS ++ ΓP) (P s1 s2 s3) -> 
  derivation (ΓP ++ [triangle; a_u; a_s]) (P s1 s2 s3).
Proof.
intros.
grab normal_derivation. move /normal_derivation_soundness => HD.
apply : (context_generalization HD).
intros.
filter_context_derivation.
apply : (weakening (Γ := [triangle])); last by list_inclusion.
apply : (eliminate_I (ds := ds)); list_inclusion.
match goal with | [ _ : In ?s ΓU |- _] => have : represents_nat s by auto end.
move => [? [? ?]]; subst; derivation_rule.
match goal with | [ _ : In ?s ΓS |- _] => have : encodes_sum s by auto end.
move => [? [? [? [? ?]]]]; subst; derivation_rule.
Qed.


Ltac decompose_USP :=
  do [
    grab shape (normal_derivation _ _ (U _)); 
    move /(generalize_ISP HS HP)/(get_interpretation HU); move /(_ ltac:(eassumption)) => [? [? ?]] |
    grab shape (normal_derivation _ _ (S _ _ _)); 
    let H := fresh in
      (move/(generalize_IUP HU HP) => H; (eapply assert_sum in H => //); try eassumption) |
    grab shape (normal_derivation _ _ (P _ _ _)); 
    let H := fresh in
      (move/(generalize_IUS HU HS) => H; (eapply assert_prod in H => //); try eassumption) ].


Lemma exists_succ : forall (P : nat -> Prop), 
  (exists (m : nat), P m /\ m > 0) -> exists (m : nat), P (Datatypes.S m).
Proof.
move => P [m [? ?]].
exists (Nat.pred m).
have : Datatypes.S (Nat.pred m) = m by omega.
by move => ->.
Qed.


Lemma finite_functional_choice : forall (f : nat -> formula) (xs : list nat),
  Forall (fun x => exists (m : nat), interpretation (f x) (1 + m)) xs
  -> exists g : (nat -> nat), Forall (fun x => interpretation (f x) (1 + g x)) xs.
Proof.
move => f. elim.
intros. exists (fun _ => 0). intros. done.

move => x xs IH. move /Forall_cons_iff.
move => [[m ?]]. move /IH => [g H_g].

exists (fun x' => if x' =? x then m else g x').
constructor. by inspect_eqb.

apply : Forall_impl; last eassumption.
move => x'. cbn. 

case : (Nat.eq_dec x x'); intro; inspect_eqb; by subst.
Qed.


Ltac egalize_interpretation :=
  match goal with 
  [H1 : interpretation ?s ?m1, H2 : interpretation ?s ?m2 |- _] =>
    tryif have ? : m1 = m2 by done then fail else have ? := interpretation_soundness H1 H2
  end.

Theorem soundness : forall (n : nat) (ΓU ΓS ΓP : list formula), 
  (forall (s : formula), In s ΓU -> represents_nat s) ->
  (forall (s : formula), In s ΓS -> encodes_sum s) ->
  (forall (s : formula), In s ΓP -> encodes_prod s) ->
  forall (ds : list diophantine),
  normal_derivation n ((Encoding.ΓI ds) ++ ΓU ++ ΓS ++ ΓP) Encoding.triangle ->
  Diophantine.solvable ds.
Proof.
have ? := interpretation_one.
elim /lt_wf_ind => n IH.

intros * => HU HS HP ds ?.
decompose_normal_derivation.
grab In; case => [? | H_In].
subst.
grab chain. move /chain_intro_sum => [s1 [s2 [s3 [s4 [s5 [? ?]]]]]]. subst.
decompose_Forall. 

do ? decompose_USP.
grab normal_derivation; inversion.
grab normal_derivation. move /(normal_weakening (Δ := (ΓI ds ++ ΓU ++ (S s1 s4 s5 :: ΓS) ++ ΓP))).
move /(_ ltac:(clear; list_inclusion)).
apply /IH; try eassumption + omega.

(*show that S s1 s4 s5 encodes sum*)
intro; case; last eauto.
intro; subst.
do 3 eexists; split; first reflexivity.
do 3 eexists; do 3 (split; first eassumption).
lia.

(*shown Gamma S inductive case*)
(*NEXT: Gamma U inductive case*)
case : H_In => [? | H_In]. 
subst. grab chain. move /chain_intro_element => [s [? [? ?]]]; subst.
decompose_Forall. do ? decompose_USP.
match goal with [_ : interpretation s ?s_m |- _] => rename s_m into m end.

grab normal_derivation; inversion.

pose sm' := represent_nat (Datatypes.S m).
grab where normal_derivation. move /(_ (get_label sm')).
(*simplify goal type*)


autorewrite with simplify_formula => ?.

do 3 (grab normal_derivation; inversion).
grab normal_derivation. move /(normal_weakening (Δ := (ΓI ds ++ (U sm' :: ΓU) ++ (S s one sm' :: ΓS) ++ (P sm' one sm' :: ΓP)))).
move /(_ ltac:(clear; list_inclusion)).

apply /IH; first omega.
1-3 : intro; case; last eauto.
1-3 : intro; subst.
exists (Datatypes.S m); split; done + omega.
1-2 : do 3 eexists; split; first reflexivity.
1-2 : have ? := interpretation_of_representation (Datatypes.S m).
1-2 : (do 3 eexists); (do 3 (split; first eassumption)); omega.
(*shown Gamma U inductive case*)
(*NEXT: Gamma P inductive case*)
case : H_In => [? | H_In].

subst.
grab chain. move /chain_intro_prod => [s1 [s2 [s3 [s4 [s5 [? ?]]]]]]. subst.
decompose_Forall. do ? decompose_USP.
grab normal_derivation; inversion.
grab normal_derivation. move /(normal_weakening (Δ := (ΓI ds ++ ΓU ++ ΓS ++ (P s1 s4 s5 :: ΓP)))).
move /(_ ltac:(clear; list_inclusion)).
apply /IH; try eassumption + omega.

(*show that P s1 s4 s5 encodes prod*)
intro; case; last eauto.
intro; subst.
do 3 eexists; split; first reflexivity.
do 3 eexists; do 3 (split; first eassumption).
nia.

case : H_In => [? | H_In].
(*lettuce show s_x_d ds*)
subst.
grab chain.
move /duplicate => [/(chain_param_wff (s_x_d_wff _)) ?].
move /inspect_chain_diophantines => [f H_f].
grab Forall. move /Forall_tl. grab Forall. move /Forall_tl. grab @eq where tl. move => ->.
move /Forall_flat_map. move => Hds.
move /Forall_flat_map. move => Hds_wff.

have : Forall (fun x => exists (m : nat), 
  interpretation (f x) (1+m)) (flat_map Diophantine.variables ds).
{
rewrite Forall_forall.
move => x.
rewrite in_flat_map. move => [d [? ?]].

grab where normal_derivation. move /(_ _ ltac:(eassumption)).
grab where (Forall well_formed_formula). move /(_ _ ltac:(eassumption)).
grab (In d) => _. 
revert dependent d. case; cbn; intros.
1-3 : decompose_Forall.
1-3 : do ? decompose_USP.
1-3 : apply : exists_succ.
1-3 : intuition subst; eexists; eauto.
}

move /finite_functional_choice.

move => [g ?].

constructor. exists g. apply Forall_forall => d Hdds.
move : (Hdds). grab Forall. move /Forall_flat_map. move => H {H}/H.
move : (Hdds). grab where normal_derivation. move => H {H}/H.
move : Hdds. grab where (Forall well_formed_formula). move => H {H}/H.
case d; cbn.
1-3 : intros.
1-3 : decompose_Forall.
1-3 : do ? decompose_USP.
1-3 : do ? egalize_interpretation.
1-3 : by inspect_eqb.


case /(@in_app_or formula): H_In => [|H_In].
move /HU => [? [? ?]]; subst; decompose_chain.
case /(@in_app_or formula): H_In.
move /HS => [? [? [? [? ?]]]]; subst; decompose_chain.
move /HP => [? [? [? [? ?]]]]; subst; decompose_chain.
Qed.
