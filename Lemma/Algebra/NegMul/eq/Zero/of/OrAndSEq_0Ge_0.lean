import Lemma.Algebra.Mul.eq.Zero.of.OrAndSEq_0Ge_0
import Lemma.Algebra.Neg.eq.Zero.of.Eq_0
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  {x y : α}
-- given
  (h : x = 0 ∧ y ≥ 0 ∨ y = 0 ∧ x ≥ 0) :
-- imply
  -(x * y) = 0 := by
-- proof
  have := Mul.eq.Zero.of.OrAndSEq_0Ge_0 h
  apply Neg.eq.Zero.of.Eq_0 this


-- created on 2025-04-19
