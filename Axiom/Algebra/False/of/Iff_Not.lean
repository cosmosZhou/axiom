import Axiom.Basic


@[main]
private lemma main
-- given
  (h : p ↔ ¬p) :
-- imply
  False := by
-- proof
  simp [Iff] at h


-- created on 2024-07-01
-- updated on 2025-01-18
