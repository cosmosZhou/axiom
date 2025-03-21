import Axiom.Basic


@[main]
private lemma main
-- given
  (h₀ : ¬q)
  (h₁ : p → q) :
-- imply
  ¬p :=
-- proof
  fun p ↦ h₀ (h₁ p)


-- created on 2024-07-01
