import Lemma.Basic


@[main]
private lemma main
  [LinearOrderedField α]
  {a b c : α}
-- given
  (h₀ : c = a + b)
  (h₁ : b > 0) :
-- imply
  c > a := by
-- proof
  linarith [h₀, h₁]


-- created on 2025-03-20
