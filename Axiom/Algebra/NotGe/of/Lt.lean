import Axiom.Basic


@[main]
private lemma main
  [PartialOrder α]
  {a b : α}
-- given
  (h : a < b) :
-- imply
  ¬a ≥ b := by
-- proof
  -- Decompose the strict order into its components: a ≤ b and a ≠ b
  let ⟨_, h⟩ := lt_iff_le_not_le.mp h
  intro h
  contradiction


-- created on 2025-03-21
