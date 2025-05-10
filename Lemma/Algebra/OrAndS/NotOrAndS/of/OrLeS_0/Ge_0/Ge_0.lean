import Lemma.Logic.NotOr.is.AndNotS
import Lemma.Logic.NotAnd.is.OrNotS
import Lemma.Algebra.OrLeS_0.OrGeS_0.OrAndS.of.OrLeS_0.Ge_0.Ge_0
import Lemma.Algebra.NotGt.is.Le
import Lemma.Algebra.NotLt.is.Ge
import Lemma.Logic.AndAnd.is.And_And
open Logic Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  {x y : α}
-- given
  (h₀ : x ≥ 0)
  (h₁ : y ≥ 0)
  (h₂ : x ≤ 0 ∨ y ≤ 0) :
-- imply
  (x ≥ 0 ∧ y ≥ 0 ∨ x < 0 ∧ y < 0) ∧ ¬(x > 0 ∧ y > 0 ∨ x < 0 ∧ y < 0) := by
-- proof
  rw [NotOr.is.AndNotS]
  rw [NotAnd.is.OrNotS, NotAnd.is.OrNotS]
  rw [NotGt.is.Le, NotGt.is.Le]
  rw [NotLt.is.Ge, NotLt.is.Ge]
  rw [And.comm]
  rw [AndAnd.is.And_And]
  apply OrLeS_0.OrGeS_0.OrAndS.of.OrLeS_0.Ge_0.Ge_0 h₀ h₁ h₂


-- created on 2025-04-19
