import Axiom.Algebra.Ge_0.Ge_0.OrLeS_0.of.OrAndS.NotOrAndS
import Axiom.Algebra.OrAndS.NotOrAndS.of.OrLeS_0.Ge_0.Ge_0
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  {x y : α} :
-- imply
  (x ≥ 0 ∧ y ≥ 0 ∨ x < 0 ∧ y < 0) ∧ ¬(x > 0 ∧ y > 0 ∨ x < 0 ∧ y < 0) ↔ x ≥ 0 ∧ y ≥ 0 ∧ (x ≤ 0 ∨ y ≤ 0) := by
-- proof
  constructor
  ·
    intro ⟨h₀, h₁⟩
    apply Ge_0.Ge_0.OrLeS_0.of.OrAndS.NotOrAndS h₁ h₀
  ·
    intro ⟨h₀, h₁, h₂⟩
    apply OrAndS.NotOrAndS.of.OrLeS_0.Ge_0.Ge_0 h₀ h₁ h₂


-- created on 2025-04-19
