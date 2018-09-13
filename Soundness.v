Require Import Utf8.

Require Import FormulaFacts.
Require Import Derivations.
Require Import Encoding.
Require Import List.
Require Import UserTactics.
Require Import Omega.
Require Import Psatz. (*lia : linear integer arithmetic*)
Require Import Diophantine.
Require Import Epsilon. (*Hilberts epsilon*)

Import ListNotations.

Require Import ListFacts.

From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


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
match goal with [ _ : In ?s ΓU |- _] => have : represents_nat s by auto end.
move => [m [? ?]]; subst.
exists m; split; last done.

do ? (gimme chain; move /chain_arr => [? [? ?]]).
gimme chain; move /chain_atom => [? _].
subst.
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
filter_context_chain; try (firstorder done).
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
intros until 0 => Hst Htu.
apply intro_arr.
apply inv_arr in Hst.
apply (weakening (Δ := (s :: Γ))) in Htu; last list_inclusion.
apply: elim_arr; eassumption.
Qed.


Lemma interpretation_soundness : forall (s : formula) (m1 m2 : nat), interpretation s m1 -> interpretation s m2 -> m1 = m2.
Proof.
intros s m1 m2 Hm1 Hm2.
inversion_clear Hm1 as [_ Hm1_2].
inversion_clear Hm2 as [Hm2_1 _].
have H : derivation calC (arr (to_dagger (represent_nat m1)) (to_dagger (represent_nat m2))).
apply: intro_arr.
set t := to_dagger (represent_nat m2) in Hm2_1 *.
set u := to_dagger (represent_nat m1) in Hm1_2 *.
set s' := (to_dagger s) in Hm2_1 Hm1_2 *.
have Hu : derivation (u :: calC) u by derivation_rule.
have Hus' : derivation (u :: calC) (arr u s').
apply: (weakening (Γ := calC)) => //. intuition.
have Hs't : derivation (u :: calC) (arr s' t).
apply: (weakening (Γ := calC)) => //. intuition.
have Hs' : derivation (u :: calC) s' by derivation_rule.
by derivation_rule.
clear s Hm1_2 Hm2_1.
suff : (1, m1) = (1, m2) by case.
apply: derivation_atom_eq H; firstorder done.
Qed.


Lemma interpretation_soundness_arr : forall (s1 s2 : formula) (m1 m2 : nat),
  derivation calC (arr (to_dagger s1) (to_dagger s2)) -> interpretation s1 m1 -> interpretation s2 m2 -> m1 = m2.
Proof.
intros until 0 => ? [? ?] [? ?].
have ? : derivation calC (arr (to_dagger (represent_nat m1)) (to_dagger s2))
by apply: derivation_arr_trans; eassumption.

have ? : derivation calC (arr (to_dagger (represent_nat m1)) (to_dagger (represent_nat m2)))
by apply: derivation_arr_trans; eassumption.

suff : get_label (represent_nat m1) = get_label (represent_nat m2) by case.
apply: derivation_atom_eq => //; firstorder done.
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
move => [s1' [s2' [s3' [?]]]].
subst; decompose_chain.
decompose_Forall.
do ? (generalize_ΓS).

decompose_derivation.
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
move => [s1' [s2' [s3' [?]]]].
subst.
decompose_chain.
decompose_Forall.
do ? (generalize_ΓP).

decompose_derivation.
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
Qed.


Lemma generalize_ISP : forall (n : nat) (ΓU ΓS ΓP : list formula), 
  (forall {s : formula}, In s ΓS -> encodes_sum s) ->
  (forall {s : formula}, In s ΓP -> encodes_prod s) ->
  forall (ds : list diophantine) (s : formula), normal_derivation n (ΓI ds ++ ΓU ++ ΓS ++ ΓP) (U s) -> derivation (ΓU ++ [triangle; a_s; a_p]) (U s).
Proof.
intros.
gimme normal_derivation. move /conservativity => HD.
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
gimme normal_derivation. move /conservativity => HD.
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
gimme normal_derivation. move /conservativity => HD.
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


Lemma epsilon_interpretation : forall s m, interpretation s m -> m > 0 -> epsilon (inhabits 0) (fun m' => interpretation s (1+m')) = m-1.
Proof.
move => s m H Hm.
have : exists m', m = 1+m' by exists (m-1); omega.
move => [m' ?]; subst.
suff : 1 + epsilon (inhabits 0) (fun m' => interpretation s (1+m')) = 1+m'.
intros. omega.
(have : exists m, interpretation s (1+m) by eauto) => H'.
have := (epsilon_spec (inhabits 0) (fun m' => interpretation s (1+m')) H').
intros.
apply : interpretation_soundness; eassumption.
Qed.

Fixpoint dio_variables (d : diophantine) :=
  match d with
  | (dio_one x) => [x]
  | (dio_sum x y z) => [x; y; z]
  | (dio_prod x y z) => [x; y; z]
  end.

Definition dio_in (x : nat) (ds : list diophantine) := In x (flat_map dio_variables ds).

(*
Inductive dio_in (x : nat) : diophantine -> Prop :=
  | dio_in_one : dio_in x (dio_one x)
  | dio_in_sum : forall (x' y' z' : nat), x = x' \/ x = y' \/ x = z' -> dio_in x (dio_sum x' y' z')
  | dio_in_prod : forall (x' y' z' : nat), x = x' \/ x = y' \/ x = z' -> dio_in x (dio_prod x' y' z').
*)


Theorem soundness : forall (n : nat) (ΓU ΓS ΓP : list formula), 
  (forall {s : formula}, In s ΓU -> represents_nat s) ->
  (forall {s : formula}, In s ΓS -> encodes_sum s) ->
  (forall {s : formula}, In s ΓP -> encodes_prod s) ->
  forall (ds : list diophantine),
  normal_derivation n ((Encoding.ΓI ds) ++ ΓU ++ ΓS ++ ΓP) Encoding.triangle ->
  Diophantine.solvable ds.
Proof.
have ? := interpretation_one.
move => n; apply (lt_wf_ind n).
move => {n} n IH.

intros until 0 => HU HS HP ds ?.
decompose_normal_derivation.
gimme In. case => [?|H_In]. subst.
gimme chain. move /chain_intro_sum => [s1 [s2 [s3 [s4 [s5 ?]]]]]. subst.

decompose_Forall.
do ? decompose_USP.
set ΓS' := S s1 s4 s5 :: ΓS.

have HS' : (∀ (s : formula), In s ΓS' → encodes_sum s).

intros s' Hs'.
destruct Hs'. 
subst s'.
unfold encodes_sum.
exists s1, s4, s5.
split; first reflexivity.
do 3 eexists.
do ? (split; first eassumption).
omega.

by apply: HS.
gimme normal_derivation.
move /inv_normal_arr => [n' [? ?]].
gimme normal_derivation => HD.
apply (normal_weakening (Δ := (ΓI ds ++ ΓU ++ ΓS' ++ ΓP))) in HD.
2:{ list_inclusion. }
have ? : n' < n by omega.
eapply IH; eassumption.

(*shown Gamma S inductive case*)
(*NEXT: Gamma U inductive case*)
case : H_In => [?|H_In]. 
subst. gimme chain. move /chain_intro_element => [s [? ?]]; subst.
decompose_Forall. do ? decompose_USP.
match goal with [_ : interpretation s ?s_m |- _] => rename s_m into m end.

gimme normal_derivation => HD.
decompose_normal_derivation.

pose sm' := represent_nat (Datatypes.S m).
move /(_ (get_label sm')) : HD.
(*simplify goal type*)
have : (instantiate (atom (get_label sm')) 0 (arr (U (var 0)) (arr (S s one (var 0)) (arr (P (var 0) one (var 0)) triangle)))) = 
(arr (U sm') (arr (S (instantiate sm' 0 s) one sm') (arr (P sm' one sm') triangle))) by reflexivity.
move => ->.
rewrite Lc.instantiate_eq0; first assumption.
move => HD.
do ? (let n := fresh "n" in move /inv_normal_arr : HD => [? [? HD]]).
eapply (normal_weakening (Δ := (ΓI ds ++ (U sm' :: ΓU) ++ (S s one sm' :: ΓS) ++ (P sm' one sm' :: ΓP)))) in HD; 
  last by list_inclusion.

apply: IH HD; first (by omega).
1-3 : move => s'.
1-3 : case; last eauto.
1-3 : move => ?; subst.
exists (Datatypes.S m); split; done + omega.
1-2 : do 3 eexists; split; first reflexivity.
1-2 : have ? := interpretation_of_representation (Datatypes.S m).
1-2 : (do 3 eexists); (do 3 (split; first eassumption)); omega.
(*shown Gamma U inductive case*)
(*NEXT: Gamma P inductive case*)
case : H_In => [|H_In].
move => ?; subst.
gimme chain. move /chain_intro_prod => [s1 [s2 [s3 [s4 [s5 ?]]]]]. subst.

decompose_Forall.
do ? decompose_USP.
set ΓP' := P s1 s4 s5 :: ΓP.

have HP' : (∀ (s : formula), In s ΓP' → encodes_prod s).
move => s'. 
case; last by auto.
move => ?; subst; do 3 eexists.
split => //.
do 3 eexists.
do ? (split; first eassumption).
nia.

gimme normal_derivation.
move /inv_normal_arr => [n' [? HD]].
apply (normal_weakening (Δ := (ΓI ds ++ ΓU ++ ΓS ++ ΓP'))) in HD.
2:{ list_inclusion. }
have ? : n' < n by omega.
eapply IH; eassumption.

case : H_In => [?|H_In].
(*lettuce show s_x_d ds*)
subst.
gimme chain.
move /inspect_chain_diophantines => [f H_f].
constructor.

(*
have : ∃ g : nat → nat, Forall (λ d : diophantine, Diophantine.eval g d = true) ds /\ (forall (x : nat), dio_in x ds -> interpretation (f x) (1 + g x)).

have : exists ds', Forall (normal_derivation (Nat.pred n) (ΓI ds' ++ ΓU ++ ΓS ++ ΓP)) params by eexists; eassumption.
clear H1.
move => [ds' H1].
gimme Forall => HD.
apply Forall_tl in HD.
rewrite H_f in HD.
clear H_f.
revert dependent ds.
elim.
intros. exists (fun _ => 0).
cbn. 
intuition.
case.
move => x ds {IH} IH.
cbn.
intros.
decompose_Forall.
do ? decompose_USP.
have := (IH ltac:(assumption)).
move => [g [Hg1 Hg2]].
match goal with [ _ : interpretation (f x) ?m |- _] => rename m into m1 end.
set g' := fun x' => if x' =? x then Nat.pred m1 else g x'.
exists g'.
split.
constructor.
cbn.
subst g'. cbn. inspect_eqb. inspect_eqb. auto.
admit. (*can be showh, but tedious*)
move => x'.
case.
intro. subst. subst g'. cbn. inspect_eqb. have : (Datatypes.S (Nat.pred m1)) = m1 by omega. move => ->. assumption.
move => Hx'.
move /(_ x' Hx') : Hg2.
subst g'. cbn.
(*preservation of interpretation*)
case : (Nat.eq_dec x' x).
move => ?. subst. inspect_eqb.
move /(interpretation_soundness).
move /(_ _ ltac:(eassumption)). intros. subst. assumption.
intro. inspect_eqb. auto.
(*can be shown*)

eapply Forall_flat_map in HD; try eassumption.
case : d HD H_d; cbn; intros.



have 
have : Forall (normal_derivation (Nat.pred n) (ΓI ds ++ ΓU ++ ΓS ++ ΓP)) params

have : exists (g : nat -> nat), forall (x : nat), dio_in x ds -> interpretation (f x) (1+ g x).
clear H2.
have ? : Forall (normal_derivation (Nat.pred n) (triangle :: ΓU ++ ΓS ++ ΓP)) (flat_map (represent_diophantine_repr f) ds) by admit.
clear H1 H_f.

(*move Heq : (ds) => ds'.
have : forall (d : diophantine), In d ds' -> In d ds by subst; auto.
clear Heq.*)
revert dependent ds.

elim.

cbn.
intros.
exists (fun _ => 0).
done.
case.
move => x ds {IH} IH .
cbn.
intros.
decompose_Forall.
have := (IH H2).
move => [g Hg].
decompose_USP.
exists (fun x' => if x' =? x then )
cbn.
intros.
apply : IH; auto.

admit.
move => [g Hg].
exists g.
*)

(*rewrite flat_map_concat_map in H_f.*)
exists (fun x => epsilon (inhabits 0) (fun m => interpretation (f x) (1+m))).
apply Forall_forall.

move => d H_d.
gimme Forall => HD.
apply Forall_tl in HD.
rewrite H_f in HD.
eapply Forall_flat_map in HD; try eassumption.
case : d HD H_d; cbn; intros.

1-3 : decompose_Forall.
1-3 : do ? decompose_USP.

(*
have HH : x < diophantine_variable_bound ds by admit.
specialize (Hg x HH).
match goal with [H1 : interpretation ?a ?m1, H2 : interpretation ?a ?m2 |- _] => have := interpretation_soundness H1 H2 end.
intro. subst.
by inspect_eqb.
have HHx : x < diophantine_variable_bound ds by admit.
have HHy : y < diophantine_variable_bound ds by admit.
have HHz : z < diophantine_variable_bound ds by admit.
have ? :=(Hg x HHx). have ? :=(Hg y HHy). have ? :=(Hg z HHz).
match goal with [H1 : interpretation ?a ?m1, H2 : interpretation ?a ?m2 |- _] => have := interpretation_soundness H1 H2; clear H1 H2 end.
match goal with [H1 : interpretation ?a ?m1, H2 : interpretation ?a ?m2 |- _] => have := interpretation_soundness H1 H2; clear H1 H2 end.
match goal with [H1 : interpretation ?a ?m1, H2 : interpretation ?a ?m2 |- _] => have := interpretation_soundness H1 H2; clear H1 H2 end.
intros. subst.
by inspect_eqb.
admit.
*)
1-3 : do ? (gimme interpretation; move /epsilon_interpretation; (nip; first nia) => ->).
1-3 : by inspect_eqb.

case /(@in_app_or formula): H_In => [|H_In].
move /HU => [? [? ?]]; subst; decompose_chain.
case /(@in_app_or formula): H_In.
move /HS => [? [? [? [? ?]]]]; subst; decompose_chain.
move /HP => [? [? [? [? ?]]]]; subst; decompose_chain.
Qed.
