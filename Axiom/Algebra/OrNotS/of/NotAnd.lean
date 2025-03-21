import Axiom.Basic


@[main]
private lemma main
-- given
  (h : ¬(p ∧ q)) :
-- imply
  ¬p ∨ ¬q := by
-- proof
  by_contra h_NotOr
  apply h_NotOr
  apply Or.inr
  intro hq
  apply h_NotOr
  apply Or.inl
  intro hpq
  apply h
  apply And.intro
  exact hpq
  exact hq


-- created on 2024-07-01
