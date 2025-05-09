import Axiom.Algebra.Inv.gt.Zero.is.Gt_0
open Algebra


/--
This lemma states that in a group with zero `α` equipped with a partial order and satisfying `ZeroLEOneClass` and `PosMulReflectLT` properties, if an element `x` is positive (`x > 0`), then its multiplicative inverse `x⁻¹` is also positive.
The proof follows directly from the equivalence `Inv.gt.Zero.is.Gt_0` which establishes the bidirectional implication between `x > 0` and `x⁻¹ > 0`.
-/
@[main]
private lemma main
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  {x : α}
-- given
  (h : x > 0) :
-- imply
  x⁻¹ > 0 :=
-- proof
  Inv.gt.Zero.is.Gt_0.mpr h


-- created on 2024-11-25
-- updated on 2025-04-04
