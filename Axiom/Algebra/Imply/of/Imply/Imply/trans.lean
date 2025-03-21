import Axiom.Basic


@[main]
private lemma main
  {p q r : Prop}
-- given
  (h₀ : p → q)
  (h₁ : q → r) :
-- imply
  p → r :=
-- proof
  fun h : p =>
    h₁ (h₀ h)


-- created on 2024-07-01
