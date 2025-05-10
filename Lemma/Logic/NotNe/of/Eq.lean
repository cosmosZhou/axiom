import Lemma.Basic


@[main]
private lemma main
  {a b : α}
-- given
  (h : a = b) :
-- imply
  ¬a ≠ b := by
-- proof
  rw [h]
  exact not_not.mpr rfl


-- created on 2025-03-30
