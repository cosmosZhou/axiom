import Axiom.Logic.NotOr.is.AndNotS
import Axiom.Logic.NotAnd.is.OrNotS
import Axiom.Algebra.NotGt.is.Le
import Axiom.Algebra.NotLt.is.Ge
import Axiom.Algebra.Ge_0.Ge_0.OrLeS_0.of.OrAndS.OrGeS_0.OrLeS_0
open Logic Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  {x y : α}
-- given
  (h₀ : ¬(x > 0 ∧ y > 0 ∨ x < 0 ∧ y < 0))
  (h₁ : x ≥ 0 ∧ y ≥ 0 ∨ x < 0 ∧ y < 0) :
-- imply
  x ≥ 0 ∧ y ≥ 0 ∧ (x ≤ 0 ∨ y ≤ 0) := by
-- proof
  rw [NotOr.is.AndNotS] at h₀
  rw [NotAnd.is.OrNotS, NotAnd.is.OrNotS] at h₀
  rw [NotGt.is.Le, NotGt.is.Le] at h₀
  rw [NotLt.is.Ge, NotLt.is.Ge] at h₀
  apply Ge_0.Ge_0.OrLeS_0.of.OrAndS.OrGeS_0.OrLeS_0 h₀.left h₀.right h₁


-- created on 2025-04-18
-- updated on 2025-04-19
