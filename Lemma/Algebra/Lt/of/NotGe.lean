import Lemma.Basic


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : ¬a ≥ b) :
-- imply
  a < b := by
-- proof
  -- Split into cases based on the linear order
  apply lt_iff_le_not_le.mpr
  constructor
  exact le_of_not_ge h
  exact h


-- created on 2025-03-21
