import Axiom.Algebra.Eq.of.Le.Ge
open Algebra


@[main]
private lemma main
  [PartialOrder α]
  {a b : α}
-- given
  (h₀ : a ≥ b)
  (h₁ : a ≤ b) :
-- imply
  a = b :=
-- proof
  Eq.of.Le.Ge h₁ h₀


-- created on 2024-11-29
