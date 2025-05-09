import Axiom.Basic


@[main]
private lemma main
  [LinearOrderedField α]
  {x : α}
-- given
  (h : x⁻¹ < 0) :
-- imply
  x < 0 := by
-- proof
  simp at h
  assumption


-- created on 2025-03-30
