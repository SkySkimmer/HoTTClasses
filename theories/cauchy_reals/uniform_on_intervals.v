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
  HoTTClasses.cauchy_reals.ring.

Local Set Universe Minimization ToSet.

Lemma uniform_on_intervals_continuous {A} `{Closeness A} (f:real -> A)
  (mu : Q+ -> Q+ -> Q+)
  {Emu : forall a : Q+,
    Uniform (f ∘ interval_proj (rat (- ' a)) (rat (' a))) (mu a)}
  : Continuous f.
Proof.
intros u e.
apply (merely_destruct (R_Qpos_bounded u)). intros [a Ea].
hnf in Emu. unfold Compose in Emu.
apply (merely_destruct (R_archimedean _ _ Ea)). intros [q [Eq Eq']].
apply rat_lt_reflecting in Eq'.
apply tr;exists (meet (mu a e) (Qpos_diff _ _ Eq')).
intros v xi.
assert (xi1 : close (mu a e) u v).
{ eapply rounded_le;[exact xi|].
  apply meet_lb_l. }
assert (xi2 : close (Qpos_diff q (' a) Eq') u v).
{ eapply rounded_le;[exact xi|].
  apply meet_lb_r. }
assert (E1 :  rat (- ' a) <= u /\ u <= rat (' a)).
{ change (rat (- ' a)) with (- (rat (' a))). apply Rabs_le_pr.
  transitivity (rat q);apply R_lt_le;trivial.
  apply rat_lt_preserving;trivial.
}
assert (E2 : rat (- ' a) <= v /\ v <= rat (' a)).
{ change (rat (- ' a)) with (- (rat (' a))). apply Rabs_le_pr.
  rewrite (Qpos_diff_pr _ _ Eq').
  apply R_lt_le.
  eapply Rlt_close_rat_plus;[exact Eq|].
  apply (non_expanding abs),xi2.
}
exact (Emu _ _ (existT _ _ E1) (existT _ _ E2) xi1).
Qed.
