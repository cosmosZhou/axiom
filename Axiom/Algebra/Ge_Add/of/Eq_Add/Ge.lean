import Axiom.Basic
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {a b b' c : α}
-- given
  (h₀ : c = a + b)
  (h₁ : b ≥ b') :
-- imply
  c ≥ a + b' := by
-- proof
  linarith [h₀, h₁]


-- created on 2025-03-20
