import Axiom.Algebra.Le.of.Sub.eq.Zero
import Axiom.Algebra.Eq.of.Le.Ge
open Algebra


@[main]
private lemma main
  {a b : ℕ}
-- given
  (h₀ : a - b = 0)
  (h₁ : a ≥ b) :
-- imply
  a = b := by
-- proof
  have := Le.of.Sub.eq.Zero h₀
  apply Eq.of.Le.Ge this h₁


-- created on 2025-04-11
