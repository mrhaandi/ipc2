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
Require Export Derivations.
Require Export Encoding.
Require Export Diophantine.
Require Import UserTactics.
Require Import MiscFacts.
Require Import Psatz. (*lia : linear integer arithmetic*)

Require Import ListFacts.
Import Encoding.

(*Notation "x ==> y" := (arr x y) (at level 0).*)

Lemma instantiate_quant (m : nat) : forall (Γ : list formula) (s : formula), 
  derivation Γ (quant s) -> derivation Γ (instantiate (represent_nat m) 0 s).
Proof.
intros.
apply : elim_quant; first eassumption.
apply : (contains_trans (s := represent_nat m)); constructor.
Qed.

Fixpoint rev_seq (last len:nat) : list nat :=
    match len with
      | 0 => nil
      | Datatypes.S len' => last :: rev_seq (Nat.pred last) len'
    end.

Lemma in_rev_seq : forall (last len n : nat), n <= last -> n > (last-len) -> In n (rev_seq last len).
Proof.
move => last len.
elim : len last.
intros; omega.

move => len IH last n *.
have : n = last \/ n < last by omega.
case; cbn; first auto.
intros; right; apply : IH; omega.
Qed.

(*representations of numbers 1 .. (1+bound)*)
Definition universe (bound : nat) := map (fun m => (U (represent_nat m))) (rev_seq (1+bound) (1+bound)).

(*representations of sums*)
Notation "x |+| y" := (S (represent_nat x) (represent_nat y) (represent_nat (y+x))) (at level 0).
(*representations of products*)
Notation "x |*| y" := (P (represent_nat x) (represent_nat y) (represent_nat (y*x))) (at level 0).
(*representations of successor equalities 1+1=2 .. bound+1='bound+1'*)
Definition successors (bound : nat) := map (fun m' => m' |+| 1) (rev_seq bound bound).
Definition product_identities (bound : nat) := map (fun m' => (m' |*| 1)) (rev_seq (1+bound) (1+bound)).

Definition represent_diophantine_eval (f : nat -> nat) (d : diophantine) : formula :=
  match d with
  | dio_one x => P (represent_nat (1 + f x)) (represent_nat (1 + f x)) one
  | dio_sum x y z => S (represent_nat (1 + f x)) (represent_nat (1 + f y)) (represent_nat (1 + f z))
  | dio_prod x y z => P (represent_nat (1 + f x)) (represent_nat (1 + f y)) (represent_nat (1 + f z))
  end.

Definition represent_diophantine_f (f : nat -> nat) (d : diophantine) (t : formula) : formula :=
  match d with
  | dio_one x => arr (U (represent_nat (1 + f x))) (arr (P (represent_nat (1 + f x)) (represent_nat (1 + f x)) one) t)
  | dio_sum x y z => arr (U (represent_nat (1 + f x))) (arr (U (represent_nat (1 + f y))) (arr (U (represent_nat (1 + f z))) (arr (S (represent_nat (1 + f x)) (represent_nat (1 + f y)) (represent_nat (1 + f z))) t)))
  | dio_prod x y z => arr (U (represent_nat (1 + f x))) (arr (U (represent_nat (1 + f y))) (arr (U (represent_nat (1 + f z))) (arr (P (represent_nat (1 + f x)) (represent_nat (1 + f y)) (represent_nat (1 + f z))) t)))
  end.

Fixpoint represent_diophantines_f (f : nat -> nat) (ds : list diophantine) : formula :=
  match ds with 
  | [] => triangle 
  | d :: ds' => represent_diophantine_f f d (represent_diophantines_f f ds')
  end.


Lemma instantiate_diophantine_representation : forall (f : nat -> nat) (ds : list diophantine), contains (s_x_d ds) (arr (arr triangle triangle) (represent_diophantines_f f ds)).
Proof.
move => f ds.
set g := fun x => Some (represent_nat (1 + f x)).

have : (arr (arr triangle triangle) (represent_diophantines_f f ds)) = instantiate_prenex g (arr (arr triangle triangle) (represent_diophantines ds)).
unfold instantiate_prenex. f_equal. fold instantiate_prenex.
revert dependent ds.
elim; [auto | case ].

1-3 : intros; cbn; do ? f_equal.
1-3 : eauto using lc_represent_diophantines.

move => ->.
apply : contains_prenex_instantiation.
eauto using lc, lc_represent_diophantines.
move => m Hm.
exists (represent_nat (1 + f m)).
eauto using lc.
Qed.


Lemma diophantine_bound_lt : forall (ds : list diophantine) (d : diophantine), In d ds ->
  match d with
  | dio_one x => x < diophantine_variable_bound ds
  | dio_sum x y z | dio_prod x y z => 
    x < diophantine_variable_bound ds /\ y < diophantine_variable_bound ds /\ z < diophantine_variable_bound ds
  end.
Proof.
elim. done.

move => d' ds IH.
case => [x|x y z|x y z].
1-3: move /(@in_cons_iff diophantine).

1-3: case; first (move => ->; cbn; lia).
1-3: move => Hd.
2-3: split; last split.
all : have : forall (d : diophantine) (ds : list diophantine) (x : nat), 
  x < diophantine_variable_bound ds -> 
  x < diophantine_variable_bound (d :: ds) by case; intros; cbn; lia.
all : apply.
all : have := (IH _ Hd); tauto.
Qed.


Lemma diophantine_restricted_eval : forall (ds : list diophantine) (f : nat -> nat), 
  let g := fun x => if x <? diophantine_variable_bound ds then f x else 0 in
  forall (ds' : list diophantine), (forall (d : diophantine), In d ds' -> In d ds) -> 
  forall (d : diophantine), In d ds' -> Diophantine.eval g d = Diophantine.eval f d.
Proof.
move => ds f g.
elim.
cbn. done.

case.
1: move => x'.
2-3:  move => x' y' z'.
1-3: move => ds' IH Hds' d'.
1-3: move /(@in_cons_iff diophantine).
1-3: case; last ((apply : IH); auto using in_cons).
1-3: move => <-; cbn.

1: have Hd' : In (dio_one x') ds by (apply : Hds'; list_inclusion).
2: have Hd' : In (dio_sum x' y' z') ds by (apply : Hds'; list_inclusion).
3: have Hd' : In (dio_prod x' y' z') ds by (apply : Hds'; list_inclusion).

1-3: have := diophantine_bound_lt Hd'.
1-3: subst g.

1: move /Nat.ltb_lt => ->.
2-3: move => [Hx' [Hy' Hz']].
2-3: move /Nat.ltb_lt : Hz' => ->.
2-3: move /Nat.ltb_lt : Hy' => ->.
2-3: move /Nat.ltb_lt : Hx' => ->.
1-3: auto.
Qed.

Lemma diophantine_restricted_bound : forall (f : nat -> nat) (n : nat), 
  let g := fun x => if x <? n then f x else 0 in
  exists (bound : nat), forall (x : nat), g x <= bound.
Proof.
move => f.
elim.
cbn.
exists 0. auto.

intros.
move : H => [b' Hb'].
exists (b' + f n).
move => x. subst g.
have : x = n \/ x < n \/ ~(x < Datatypes.S n) by omega.
(case; last case) => Hx.
have : x < Datatypes.S n by omega.
move /Nat.ltb_lt => ->; subst; lia.
move : (Hb' x).
move /Nat.ltb_lt : (Hx) => ->.
(have : x < Datatypes.S n by omega); move /Nat.ltb_lt => ->.
lia.
move : Hx.
rewrite <- Nat.ltb_lt.
case : (x <? Datatypes.S n); [done | intros; omega].
Qed.

Lemma finite_solution : forall (ds : list diophantine), Diophantine.solvable ds -> 
  exists (bound : nat) (g : nat -> nat), Forall (fun d => Diophantine.eval g d = true) ds /\ (forall (x : nat), g x <= bound).
Proof.
move => ds. case. move => [f Hf].
have := diophantine_restricted_bound f (diophantine_variable_bound ds).
set g := fun x => if x <? diophantine_variable_bound ds then f x else 0.
move => [bound Hg2].
exists bound, g.
split; auto.
have : forall (d : diophantine), In d ds -> Diophantine.eval g d = Diophantine.eval f d.
apply : diophantine_restricted_eval; auto.
move : Hf.
rewrite -> ? Forall_forall; eauto.
Qed.

Lemma in_successors : forall (bound : nat) (m : nat), m > 0 ->  m <= bound -> In (m |+| 1) (successors bound).
Proof.
elim.
intros; omega.
move => bound IH m ? ?.
have : m = 1 + bound \/ m < 1 + bound by omega.
case; move => ?; subst; cbn.
by left.
right. apply : IH; omega.
Qed.

Lemma in_product_identities : forall (bound : nat) (m : nat), m > 0 ->  m <= 1+bound -> In (m |*| 1) (product_identities bound).
Proof.
elim.
intros.
have ? : m = 1 by omega. subst.
cbn; auto.

move => bound IH m ? ?.
have : m = 2 + bound \/ m < 2 + bound by omega.
case; move => ?; subst; cbn.
by left.
right. apply : IH; omega.
Qed.

Lemma in_universe : forall (bound : nat) (m : nat), m >= 1 -> m <= 1+bound -> In (U (represent_nat m)) (universe bound).
Proof.
elim.
intros.
left.
do ? f_equal. omega.
move => bound IH m ? ?.
have : m = 2 + bound \/ m < 2 + bound by omega.
case; move => ?; subst; cbn.
by left.
right. apply : IH; omega.
Qed.

(*to derive triangle from simpler ΓU, suffices to derive triangle from more complex ΓU. phase 1*)
Theorem completeness_U (ds : list diophantine) : forall (bound : nat), 
  let ΓS := successors bound in
  let ΓP := product_identities bound in
  derivation (ΓI ds ++ universe bound ++ ΓS ++ ΓP) triangle ->
  derivation (ΓI ds ++ [U one; P one one one]) triangle.
Proof.
elim.
move => ΓS ΓP.
apply.
set ΓI_ds := ΓI ds.

move => bound IH ΓS ΓP HD.
apply : (IH); try reflexivity.
set ΓU' := universe bound.
set ΓS' := successors bound.
set ΓP' := product_identities bound.
set Γ' := ΓI_ds ++ ΓU' ++ ΓS' ++ ΓP'.

have : derivation (Γ') s_x_u by derivation_rule.
move /(instantiate_quant (1+bound)).

autorewrite with simplify_formula.

move /elim_arr.
nip.

have ? : In (U (represent_nat (1 + bound))) ΓU' by subst; list_inclusion.
derivation_rule.

move /elim_arr.
nip; last done.

apply : (intro_quant_fresh (a:=get_label (represent_nat (2 + bound)))).
(*finniky*)
subst Γ'.

apply Forall_app_iff; split.

(*ΓI*) subst ΓI_ds; clear.
inspect_freshness.
elim ds.
inspect_freshness.
intros; grab diophantine; case; intros; cbn; inspect_freshness; auto.

have : 2 + bound > 1 + bound by omega.
move : (2 + bound) => n Hn.
apply Forall_app_iff; split.

(*ΓU*) move : Hn; subst ΓU'; clear.
elim : bound n; cbn; intros; (constructor; [inspect_freshness | auto with arith]).

apply Forall_app_iff; split. 

(*ΓS*) move : Hn; subst ΓS'; clear.
elim : bound n; cbn; intros; constructor; [inspect_freshness | auto with arith].

(*ΓP*) move : Hn; subst ΓP'; clear.
elim : bound n; cbn; intros; (constructor; [inspect_freshness | auto with arith]).

(*freshness in goal*)
inspect_freshness.

have : atom (get_label (represent_nat (2 + bound))) = represent_nat (2 + bound) by reflexivity.
move => ->.
autorewrite with simplify_formula.
do 3 (apply : intro_arr).
apply : (weakening HD).

have : ΓP = P (represent_nat (2 + bound)) one (represent_nat (2 + bound)) :: ΓP' by cbn; (do ? f_equal); omega.
move => ->.
list_inclusion.
Qed.

Theorem completeness_S (ds : list diophantine) : forall (bound : nat) (m1 m2 : nat) (Γ' : list formula), 
  (1+m1)+(1+m2) <= 1+bound ->
  let ΓS := successors bound in
  let ΓP := product_identities bound in
  derivation (ΓI ds ++ (universe bound) ++ ΓS ++ ΓP ++ (((1+m1) |+| (1+m2)) :: Γ')) triangle ->
  derivation (ΓI ds ++ (universe bound) ++ ΓS ++ ΓP ++ Γ') triangle.
Proof.
move => bound m1 m2.
elim : m2 m1 => [|m2 IH] => m1 Γ' Hm1m2 ΓS ΓP HD.
apply : (weakening HD).
move => s.
have : In ((1 + m1) |+| (1 + 0)) ΓS by apply : in_successors; omega.
list_inclusion.

apply : IH.
have : 1 + m1 + (1 + m2) ≤ 1 + bound by omega. apply.
fold ΓS.
set Γ := ΓI ds ++ universe bound ++ ΓS ++ ΓP ++ ((1 + m1) |+| (1 + m2) :: Γ').
have : derivation Γ s_x_s by derivation_rule.

move /(instantiate_quant (1+m1)).
move /(instantiate_quant (1+m2)).
move /(instantiate_quant (1 + m2 + (1 + m1))).
move /(instantiate_quant (2+m2)).
move /(instantiate_quant ((2+m2)+(1+m1))).
autorewrite with simplify_formula.

do_first 9 (move /elim_arr; nip; first last).
apply.

apply /intro_arr.
apply : (weakening HD).
list_inclusion.

1-2 : apply : ax.
1-2 : apply : (in_sub (A := successors bound)); try list_inclusion.
1-2 : apply /in_successors; omega.

apply : ax. list_inclusion.

1-5 : apply : ax.
1-5 : apply : (in_sub (A := universe bound)); try list_inclusion.
1-5 : apply /in_universe; omega.
Qed.


Theorem completeness_P (ds : list diophantine) : forall (bound : nat) (m1 m2 : nat) (Γ' : list formula), 
  (1+m1)*(1+m2) <= 1+bound ->
  let ΓS := successors bound in
  let ΓP := product_identities bound in
  derivation (ΓI ds ++ (universe bound) ++ ΓS ++ ΓP ++ (((1+m1) |*| (1+m2)) :: Γ')) triangle ->
  derivation (ΓI ds ++ (universe bound) ++ ΓS ++ ΓP ++ Γ') triangle.
Proof.
move => bound m1 m2.
elim : m2 m1 => [|m2 IH] => m1 Γ' Hm1m2 ΓS ΓP HD.
apply : (weakening HD).
move => s.
have : In ((1 + m1) |*| (1 + 0)) ΓP by apply : in_product_identities; omega.
list_inclusion.

apply : IH.
have : (1 + m1) * (1 + m2) ≤ 1 + bound by nia. apply.
fold ΓS ΓP.
apply : (completeness_S (m1:=m1+m2+m1*m2) (m2:=m1)).
nia.
set Γ := ΓI ds ++ universe bound ++ ΓS ++ ΓP ++ ((1 + (m1 + m2 + m1 * m2)) |+| (1 + m1) :: (1 + m1) |*| (1 + m2) :: Γ').
have : derivation Γ s_x_p by derivation_rule.

move /(instantiate_quant (1+m1)).
move /(instantiate_quant (1+m2)).
move /(instantiate_quant ((1 + m2) * (1 + m1))).
move /(instantiate_quant (2+m2)).
move /(instantiate_quant ((2+m2)*(1+m1))).
autorewrite with simplify_formula.

do_first 9 (move /elim_arr; nip; first last).
move => H'.
apply : (weakening H').
list_inclusion.

apply /intro_arr.
apply : (weakening HD).
list_inclusion.

apply : ax.
apply : (in_sub (A := [(1 + (m1 + m2 + m1 * m2)) |+| (1 + m1)])); [left | list_inclusion].
f_equal; f_equal; nia.

apply : ax.
apply : (in_sub (A := successors bound)); try list_inclusion.
apply /in_successors; nia.

apply : ax. list_inclusion.

1-5 : apply : ax.
1-5 : apply : (in_sub (A := universe bound)); try list_inclusion.
1-5 : apply /in_universe; nia.
Qed.

Lemma completeness : forall (ds : list diophantine), Diophantine.solvable ds ->
  derivation (ΓI ds ++ [U one; P one one one]) triangle.
Proof.
move => ds.
move /finite_solution => [bound [g [Hg1 Hg2]]].
apply : (completeness_U (bound:=bound)).
set Γ' := map (represent_diophantine_eval g) ds.
set ΓU := universe bound.
set ΓS := successors bound.
set ΓP := product_identities bound.

(*extent type environment by necessary assumptions*)
suff : derivation (ΓI ds ++ ΓU ++ ΓS ++ ΓP ++ Γ') triangle.

move : (ds) => ds'.
revert dependent ds.
elim.
move => ? ? HD.
apply : (weakening HD). list_inclusion.
case.

1 : move => x ds IH.
2-3 : move => x y z ds IH.
1-3 : move /(Forall_cons_iff) => [Hd ?].
1-3 : move /Nat.eqb_eq in Hd.
1-3 : move => Γ' HD.
1-3 : apply : (IH); try assumption.
1-3 : cbn in Γ'.

2-3 : have ? := (Hg2 z).
1 : have ? : (1 + g x) * (1 + g x) ≤ 1 + bound by nia.
2 : have ? : (1 + g x) + (1 + g y) ≤ 1 + bound by nia.
3 : have ? : (1 + g x) * (1 + g y) ≤ 1 + bound by nia.
1 : apply : (completeness_P); try eassumption.
2 : apply : (completeness_S); try eassumption.
3 : apply : (completeness_P); try eassumption.

1 : have : (1 + g x) |*| (1 + g x) = P (represent_nat (Datatypes.S (g x))) (represent_nat (Datatypes.S (g x))) one
  by cbn; unfold one; (do ? f_equal); nia.
2 : have : (1 + g x) |+| (1 + g y) = S (represent_nat (Datatypes.S (g x))) (represent_nat (Datatypes.S (g y))) (represent_nat (Datatypes.S (g z)))
  by cbn; unfold one; (do ? f_equal); nia.
3 : have : (1 + g x) |*| (1 + g y) = P (represent_nat (Datatypes.S (g x))) (represent_nat (Datatypes.S (g y))) (represent_nat (Datatypes.S (g z)))
  by cbn; unfold one; (do ? f_equal); nia.
1-3 : move => ->; assumption.

(*show derivability in extgended environment*)
have : derivation (ΓI ds ++ ΓU ++ ΓS ++ ΓP ++ Γ') (s_x_d ds) by derivation_rule.

move /(elim_quant).
move /(_ _ (instantiate_diophantine_representation g ds)).

move /elim_arr; nip; first derivation_rule.
move : (ΓI ds) => ΓI_ds.
have : forall s, In s (map (represent_diophantine_eval g) ds) -> In s Γ' by auto.
move : (Γ') => {Γ'} Γ'.
(*induction not entirely clear, Gamma' changes?*)
revert dependent ds.
elim; first auto.
case.

1 : move => x ds IH.
2-3 : move => x y z ds IH.
2-3 : have ? := Hg2 z.
1-3 : move /(Forall_cons_iff) => [Hd ?] HΓ' HD.
1-3 : move /Nat.eqb_eq in Hd.
1-3 : cbn in HΓ'.
1-3 : apply : IH; try assumption + auto.
1-3 : grab derivation.
1-3 : unfold represent_diophantines_f; fold represent_diophantines_f; unfold represent_diophantine_f.

1 : (do_first 2 (move /elim_arr; nip; first last)); first apply.
3-4 : (do_first 4 (move /elim_arr; nip; first last)); first apply. 

all : match goal with 
  | [ |- derivation _ (U _) ] => apply (weakening (Γ:=ΓU)); last list_inclusion 
  | [ |- derivation _ (P _ _ _) ] => apply (weakening (Γ:=Γ')); last list_inclusion
  | [ |- derivation _ (S _ _ _) ] => apply (weakening (Γ:=Γ')); last list_inclusion
end.

all : apply ax; auto.
all : apply : in_universe; lia + nia.
Qed.
