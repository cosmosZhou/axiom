import Axiom.Basic


@[main]
private lemma main
-- given
  (h : p ∨ q) :
-- imply
  ¬p → q := by
-- proof
  intro hp
  match h with
  | Or.inl hnp =>
    contradiction
  | Or.inr hq =>
    exact hq


-- created on 2025-04-07
