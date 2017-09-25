Require Import
  HoTT.Types.Universe
  HoTT.Basics.Decidable
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.integers
  HoTT.Classes.interfaces.naturals
  HoTT.Classes.interfaces.rationals
  HoTT.Classes.interfaces.orders
  HoTT.Classes.implementations.natpair_integers
  HoTT.Classes.theory.rings
  HoTT.Classes.theory.integers
  HoTT.Classes.theory.dec_fields
  HoTT.Classes.orders.dec_fields
  HoTT.Classes.theory.rationals
  HoTT.Classes.orders.lattices
  HoTT.Classes.theory.additional_operations
  HoTT.Classes.theory.premetric
  HoTT.Classes.implementations.assume_rationals
  HoTTClasses.cauchy_completion.

Require Export
  HoTTClasses.cauchy_reals.base
  HoTTClasses.cauchy_reals.abs
  HoTTClasses.cauchy_reals.order
  HoTTClasses.cauchy_reals.metric
  HoTTClasses.cauchy_reals.ring
  HoTTClasses.cauchy_reals.full_order.

Local Set Universe Minimization ToSet.

Lemma apart_to_metric : forall x y : real, apart x y -> 0 < abs (x - y).
Proof.
intros x y [E|E];apply flip_pos_minus in E.
- rewrite <-Rabs_neg,<-negate_swap_r. rewrite Rabs_of_nonneg;trivial.
  apply R_lt_le;trivial.
- rewrite Rabs_of_nonneg;trivial.
  apply R_lt_le;trivial.
Qed.

Lemma Rlt_join_either : forall a b c, a < join b c -> hor (a < b) (a < c).
Proof.
intros a b c E.
generalize (cotransitive E b);apply (Trunc_ind _);intros [E1|E1].
- apply tr. auto.
- generalize (cotransitive E c);apply (Trunc_ind _);intros [E2|E2].
  + apply tr. auto.
  + destruct (irreflexivity lt _ (Rlt_join _ _ _ E1 E2)).
Qed.

Lemma Rlt_join_l : forall a b, a < join a b -> a < b.
Proof.
intros a b E;apply (merely_destruct (Rlt_join_either _ _ _ E));
intros [E1|E1];trivial.
destruct (irreflexivity lt _ E1).
Qed.

Lemma Rlt_join_r : forall a b, b < join a b -> b < a.
Proof.
intros a b E;apply (merely_destruct (Rlt_join_either _ _ _ E));
intros [E1|E1];trivial.
destruct (irreflexivity lt _ E1).
Qed.

Lemma metric_to_apart : forall x y : real, 0 < abs (x - y) ->
  apart x y.
Proof.
intros x y E.
rewrite Rabs_is_join in E. apply (merely_destruct (Rlt_join_either _ _ _ E)).
intros [E1|E1].
- rewrite <-negate_swap_r in E1. apply flip_pos_minus in E1. left;trivial.
- apply flip_pos_minus in E1. right;trivial.
Qed.

Lemma Rabs_triangle_alt : forall x y : real, abs (abs x - abs y) <= abs (x - y).
Proof.
intros x y.
apply R_not_lt_le_flip.
intros E. apply (merely_destruct (R_archimedean_pos _ _ (Rabs_nonneg _) E)).
intros [e [E1 E2]].
apply metric_to_equiv in E1. apply (non_expanding abs) in E1.
apply equiv_to_metric in E1.
apply (irreflexivity lt (rat (' e))).
etransitivity;eauto.
Qed.

Instance Rabs_strong_ext : StrongExtensionality (abs (A:=real)).
Proof.
intros x y E.
apply metric_to_apart.
eapply R_lt_le_trans;[|apply Rabs_triangle_alt].
apply apart_to_metric in E. trivial.
Qed.

Lemma Rmult_pos_decompose_nonneg : forall x y, 0 <= x ->
  0 < x * y ->
  0 < y.
Proof.
intros x y E1 E2.
assert (E3 : merely (exists e : Q+, rat (' e) < x * y)).
{ generalize (R_archimedean _ _ E2);apply (Trunc_ind _);intros [e [E3 E4]].
  apply rat_lt_reflecting in E3.
  apply tr. exists (mkQpos e E3). trivial. }
revert E3;apply (Trunc_ind _);intros [e E3].
apply (merely_destruct (R_Qpos_bounded x)). intros [n E4].
apply R_lt_le_trans with (rat (' (e/n)));[apply rat_lt_preserving;solve_propholds|].
apply R_not_lt_le_flip. intros E5.
apply (irreflexivity lt (rat (' e))).
eapply R_lt_le_trans;[apply E3|].
rewrite <-(pos_unconjugate n e). rewrite <-Qpos_mult_assoc.
change (x * y <= rat (' n) * rat (' (e / n))).
apply mult_le_compat;trivial.
- apply R_not_lt_le_flip;intros E6.
  apply (irreflexivity lt 0).
  apply R_lt_le_trans with (x * y);trivial.
  apply nonneg_nonpos_mult;trivial. apply R_lt_le;trivial.
- transitivity (abs x).
  + apply Rabs_le_raw.
  + apply R_lt_le;trivial.
- apply R_lt_le;trivial.
Qed.

Lemma Rabs_mult : forall x y : real, abs (x * y) = abs x * abs y.
Proof.
apply unique_continuous_binary_extension.
- change (Continuous (abs ∘ uncurry (@mult real _)));apply _.
- change (Continuous (uncurry (@mult real _) ∘ map2 abs abs));apply _.
- intros. change (rat (abs (q * r)) = rat (abs q * abs r)).
  exact (ap rat (Qabs_mult q r)).
Qed.

Lemma Rmult_lt_apart : forall z x y, z * x < z * y -> apart x y.
Proof.
intros z x y E.
symmetry.
apply metric_to_apart.
apply Rmult_pos_decompose_nonneg with (abs z);[apply Rabs_nonneg|].
rewrite <-Rabs_mult.
apply R_lt_le_trans with (z * (y - x));[|apply Rabs_le_raw].
rewrite plus_mult_distr_l,<-negate_mult_distr_r.
apply (snd (flip_pos_minus _ _)).
trivial.
Qed.

Global Instance real_full_pseudo_srorder : FullPseudoSemiRingOrder Rle Rlt.
Proof.
apply from_full_pseudo_ring_order;try apply _.
apply @apartness.strong_binary_setoid_morphism_commutative;try apply _.
intros z x y [E|E];apply Rmult_lt_apart in E;trivial;symmetry;trivial.
Qed.
