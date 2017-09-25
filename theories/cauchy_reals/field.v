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
  HoTTClasses.cauchy_completion.

Require Export
  HoTTClasses.cauchy_reals.base
  HoTTClasses.cauchy_reals.abs
  HoTTClasses.cauchy_reals.order
  HoTTClasses.cauchy_reals.metric
  HoTTClasses.cauchy_reals.ring
  HoTTClasses.cauchy_reals.full_order
  HoTTClasses.cauchy_reals.full_ring
  HoTTClasses.cauchy_reals.recip.

Local Set Universe Minimization ToSet.

Global Instance real_field : Field real.
Proof.
split;try apply _.
apply R_recip_inverse.
Qed.
