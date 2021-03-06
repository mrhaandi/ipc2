Load Common.

Require Import FormulaFacts.
Require Import Derivations.
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
gimme derivation.
simpl.
move /inv_quant/(_ a).
rewrite ? instantiate_quantification.
(have : (n + 0) = n by omega) => ->.
move => HD.
simpl.
apply : H => //.
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


Lemma get_interpretation : forall (s : formula) (ΓU : list formula),
  (forall {s : formula}, In s ΓU -> represents_nat s) ->
  derivation (ΓU ++ [triangle; a_s; a_p]) (U s) ->
  exists (m : nat), interpretation s m /\ m > 0.
Proof.
move => s ΓU HΓU HD.
decompose_derivation.
filter_context_chain => ?.
move : (HΓU _ ltac:(eassumption)) => [m [? ?]]; subst.
exists m; split; last done.
decompose_chain.
decompose_Forall.
do 2 generalize_ΓU.
decompose_derivation.
do 2 filter_context_chain.
decompose_Forall.
gimme derivation; gimme derivation => HD2 HD1.
constructor.
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
Qed.


Lemma derivation_atom_eq : forall (a b : label), ~(In (Formula.atom a) (dagger :: calC)) -> ~(In (Formula.atom b) (dagger :: calC)) -> 
  derivation calC (Formula.arr (to_dagger (Formula.atom a)) (to_dagger (Formula.atom b))) -> a = b.
Proof.
intros.
decompose_derivation.
filter_context_chain. exfalso; intuition.
decompose_Forall.
decompose_derivation.
filter_context_chain; (firstorder done).
Qed.


Lemma derivation_represent_nat_eq : forall (m1 m2 : nat), 
  derivation calC (Formula.arr (to_dagger (represent_nat m1)) (to_dagger (represent_nat m2))) -> m1 = m2.
Proof.
intros.
suff : get_label (represent_nat m1) = get_label (represent_nat m2) by case.
apply: derivation_atom_eq => //; firstorder done.
Qed.


Lemma chain_intro_sum (params : list formula) : chain s_x_s (get_label triangle) params -> 
  exists (s1 s2 s3 s4 s5 : formula), 
    (params = [U s1; U s2; U s3; U s4; U s5; S s1 s2 s3; S s2 one s4; S s3 one s5; Formula.arr (S s1 s4 s5) triangle]).
Proof.
case; intros; first do ? decompose_contains.
gimme chain; do ? decompose_contains.
move => ?; decompose_chain.
by do 5 eexists.
Qed.


Lemma chain_intro_prod (params : list formula) : chain s_x_p (get_label triangle) params -> 
  exists (s1 s2 s3 s4 s5 : formula), 
    (params = [U s1; U s2; U s3; U s4; U s5; P s1 s2 s3; S s2 one s4; S s3 s1 s5; Formula.arr (P s1 s4 s5) triangle]).
Proof.
case; intros; first do ? decompose_contains.
gimme chain; do ? decompose_contains.
move => ?; decompose_chain.
by do 5 eexists.
Qed.


Lemma chain_intro_element (params : list formula): chain s_x_u (get_label triangle) params -> 
  exists (s : formula), lc 0 s /\
    (params = [U s; quant ( arr (U (var 0)) (arr (S s one (var 0)) (arr (P (var 0) one (var 0)) triangle)))]).
Proof.
case; intros; first do ? decompose_contains.
gimme chain; do ? decompose_contains.
move => ?; decompose_chain.
eexists. by split; [eassumption | ].
Qed.


Lemma derivation_arr_trans : forall (Γ : list formula) (s t u : formula),
  derivation Γ (arr s t) -> derivation Γ (arr t u) -> derivation Γ (arr s u).
Proof.
intros * => Hst Htu.
apply intro_arr.
apply inv_arr in Hst.
apply (weakening (Δ := (s :: Γ))) in Htu; last list_inclusion.
apply: elim_arr; eassumption.
Qed.


Lemma interpretation_soundness : forall (s : formula) (m1 m2 : nat), interpretation s m1 -> interpretation s m2 -> m1 = m2.
Proof.
move => s m1 m2 [_ Hm1_2] [Hm2_1 _].
move : (derivation_arr_trans Hm1_2 Hm2_1).
by move /derivation_represent_nat_eq.
Qed.


Lemma interpretation_soundness_arr : forall (s1 s2 : formula) (m1 m2 : nat),
  derivation calC (arr (to_dagger s1) (to_dagger s2)) -> interpretation s1 m1 -> interpretation s2 m2 -> m1 = m2.
Proof.
intros * => s1s2 [_ m1s1] [s2m2 _].
move : (derivation_arr_trans m1s1 s1s2) => m1s2.
move : (derivation_arr_trans m1s2 s2m2).
by move /derivation_represent_nat_eq.
Qed.


Lemma assert_sum : forall (s1 s2 s3 : formula) (m1 m2 m3 : nat) (ΓU ΓS ΓP : list formula),
  (forall {s : formula}, In s ΓS -> encodes_sum s) ->
  interpretation s1 m1 -> interpretation s2 m2 -> interpretation s3 m3 -> 
  derivation (ΓS ++ [triangle; a_u; a_p]) (S s1 s2 s3) ->
  m1 + m2 = m3.
Proof.
intros until 3 => Hs1 Hs2 Hs3 HD.
decompose_derivation.
filter_context_chain => Hc.
match goal with [ _ : In ?s ΓS |- _] => have : encodes_sum s by auto end.
move => [s1' [s2' [s3' [?]]]] [m1' [m2' [m3' [Hs1' [Hs2' [Hs3' ?]]]]]].
subst. decompose_chain.
decompose_Forall.
do ? (generalize_ΓS).

decompose_derivation.
do ? (filter_context_chain).
decompose_Forall.

do 3 (gimme derivation).
do 3 (move /intro_arr => ?).
suff : m1' = m1. suff : m2' = m2. suff : (m1' + m2') = m3.
intros. by subst.

all: apply: (interpretation_soundness_arr); try eassumption.
all: apply: (context_generalization); [eassumption | by intros; filter_context_derivation].
Qed.


Lemma assert_prod : forall (s1 s2 s3 : formula) (m1 m2 m3 : nat) (ΓU ΓS ΓP : list formula),
  (forall {s : formula}, In s ΓP -> encodes_prod s) ->
  interpretation s1 m1 -> interpretation s2 m2 -> interpretation s3 m3 -> 
  derivation (ΓP ++ [triangle; a_u; a_s]) (P s1 s2 s3) ->
  m1 * m2 = m3.
Proof.
intros until 3 => Hs1 Hs2 Hs3 HD.
decompose_derivation.
filter_context_chain => Hc.
match goal with [ _ : In ?s ΓP |- _] => have : encodes_prod s by auto end.
move => [s1' [s2' [s3' [?]]]] [m1' [m2' [m3' [Hs1' [Hs2' [Hs3' ?]]]]]].
subst. decompose_chain.
decompose_Forall.
do ? (generalize_ΓP).

decompose_derivation.
do ? (filter_context_chain).
decompose_Forall.

do 3 (gimme derivation).
do 3 (move /intro_arr => ?).
suff : m1' = m1. suff : m2' = m2. suff : (m1' * m2') = m3.
intros. by subst.

all: apply: (interpretation_soundness_arr); try eassumption.
all: apply: (context_generalization); [eassumption | by intros; filter_context_derivation].
Qed.


Lemma generalize_ISP : forall (n : nat) (ΓU ΓS ΓP : list formula), 
  (forall {s : formula}, In s ΓS -> encodes_sum s) ->
  (forall {s : formula}, In s ΓP -> encodes_prod s) ->
  forall (ds : list diophantine) (s : formula), normal_derivation n (ΓI ds ++ ΓU ++ ΓS ++ ΓP) (U s) -> derivation (ΓU ++ [triangle; a_s; a_p]) (U s).
Proof.
intros.
gimme normal_derivation. move /normal_derivation_soundness => HD.
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
gimme normal_derivation. move /normal_derivation_soundness => HD.
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
gimme normal_derivation. move /normal_derivation_soundness => HD.
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
    gimme shape (normal_derivation _ _ (U _)); 
    move /(generalize_ISP HS HP)/(get_interpretation HU)=> [? [? ?]] |
    gimme shape (normal_derivation _ _ (S _ _ _)); 
    let H := fresh in
      (move/(generalize_IUP HU HP) => H; (eapply assert_sum in H => //); try eassumption) |
    gimme shape (normal_derivation _ _ (P _ _ _)); 
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
gimme In; case => [? | H_In].
subst.
gimme chain. move /chain_intro_sum => [s1 [s2 [s3 [s4 [s5 ?]]]]]. subst.
decompose_Forall. do ? decompose_USP.
gimme normal_derivation; inversion.
gimme normal_derivation. move /(normal_weakening (Δ := (ΓI ds ++ ΓU ++ (S s1 s4 s5 :: ΓS) ++ ΓP))).
move /(_ ltac:(clear; list_inclusion)).
apply /IH; try eassumption + omega.

(*show that S s1 s4 s5 encodes sum*)
intro; case; last eauto.
intro; subst. apply : encodes_sum_intro; eassumption + lia.
(*shown Gamma S inductive case*)

(*NEXT: Gamma U inductive case*)
case : H_In => [? | H_In]. 
subst. gimme chain. move /chain_intro_element => [s [? ?]]; subst.
decompose_Forall. do ? decompose_USP.
match goal with [_ : interpretation s ?s_m |- _] => rename s_m into m end.

gimme normal_derivation; inversion.

pose sm' := represent_nat (Datatypes.S m).
gimme where normal_derivation. move /(_ (get_label sm')).
(*simplify goal type*)
autorewrite with simplify_formula => ?.

do 3 (gimme normal_derivation; inversion).
gimme normal_derivation. move /(normal_weakening (Δ := (ΓI ds ++ (U sm' :: ΓU) ++ (S s one sm' :: ΓS) ++ (P sm' one sm' :: ΓP)))).
move /(_ ltac:(clear; list_inclusion)).

apply /IH; first omega.
1-3 : intro; case; last eauto.
1-3 : intro; subst.

apply : represents_nat_intro; [reflexivity | lia].
apply : encodes_sum_intro; try eassumption + apply : interpretation_of_representation + lia.
apply : encodes_prod_intro; try eassumption + apply : interpretation_of_representation + lia.

(*shown Gamma U inductive case*)
(*NEXT: Gamma P inductive case*)
case : H_In => [? | H_In].

subst.
gimme chain. move /chain_intro_prod => [s1 [s2 [s3 [s4 [s5 ?]]]]]. subst.
decompose_Forall. do ? decompose_USP.
gimme normal_derivation; inversion.
gimme normal_derivation. move /(normal_weakening (Δ := (ΓI ds ++ ΓU ++ ΓS ++ (P s1 s4 s5 :: ΓP)))).
move /(_ ltac:(clear; list_inclusion)).
apply /IH; try eassumption + omega.

(*show that P s1 s4 s5 encodes prod*)
intro; case; last eauto.
intro; subst. apply : encodes_prod_intro; eassumption + nia.

case : H_In => [? | H_In].
(*lettuce show s_x_d ds*)
subst.
gimme chain.
move /inspect_chain_diophantines => [f H_f].
gimme Forall; move /Forall_tl. gimme @eq where tl. move => ->.
move /Forall_flat_map. move => Hds.

have : Forall (fun x => exists (m : nat), 
  interpretation (f x) (1+m)) (flat_map Diophantine.variables ds).
{
rewrite Forall_forall.
move => x.
rewrite in_flat_map. move => [d [? ?]].
gimme where (In d ds).
gimme where normal_derivation. move //.
revert dependent d. case; cbn; intros.
1-3 : decompose_Forall.
1-3 : do ? decompose_USP.
1-3 : apply : exists_succ.
1-3 : intuition subst; eexists; eauto.
}

move /finite_functional_choice.

move => [g ?].

constructor. exists g. apply Forall_forall => d Hdds.
move : (Hdds). gimme Forall. move /Forall_flat_map. move //.
move : Hdds. gimme where normal_derivation. move //.
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
