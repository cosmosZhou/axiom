import Axiom.Algebra.Lt.of.Le.Lt
import Axiom.Algebra.Le.of.Le.Le
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  {a b a' b' : α}
-- given
  (h₀ : a' ≤ a)
  (h₁ : b' ≥ b) :
-- imply
  Ioc a b ⊆ Ioc a' b' := by
-- proof
  intro x hx
  constructor
  apply Lt.of.Le.Lt h₀ hx.left
  apply Le.of.Le.Le hx.right h₁


-- created on 2025-03-02
