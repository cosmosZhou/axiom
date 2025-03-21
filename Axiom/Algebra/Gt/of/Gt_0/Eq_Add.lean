import Axiom.Basic
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {a b c : α}
-- given
  (h₀ : a > 0)
  (h₁ : c = a + b) :
-- imply
  c > b := by
-- proof
  linarith [h₀, h₁]


-- created on 2025-03-20
