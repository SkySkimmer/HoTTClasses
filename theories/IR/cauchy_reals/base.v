Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.theory.rings
  HoTTClasses.theory.rationals
  HoTTClasses.IR.cauchy_completion.

Definition real := C Q.

Global Instance Rplus@{} : Plus real
  := lipschitz_extend_binary _ _ (fun q r => eta (q + r)) 1 1.

Lemma anom `{!Negate real} `{!Associative Rplus} : forall z x : real, - z + (z + x) = (- z + z) + x.
Proof.
  intros z x; rewrite !(simple_associativity (f:=plus) (-z) z).
Abort.
