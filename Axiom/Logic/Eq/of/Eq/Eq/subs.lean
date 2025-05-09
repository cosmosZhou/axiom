import Axiom.Logic.Imp_And.of.Imp
open Logic


@[main]
private lemma main
  {a b : α}
  {p q : α → β}
-- given
  (h₀ : a = b)
  (h₁ : p a = q a) :
-- imply
  p b = q b := by
-- proof
  exact h₀ ▸ h₁


-- created on 2025-01-12
