import Lemma.Algebra.LeMulS.of.Ge.Le_0
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  {x a b : α}
-- given
  (h₀ : a ≤ b)
  (h₁ : x ≤ 0) :
-- imply
  a * x ≥ b * x :=
-- proof
  LeMulS.of.Ge.Le_0 h₀ h₁


-- created on 2025-03-30
