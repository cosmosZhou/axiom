import Lemma.Basic


@[main]
private lemma main:
-- imply
  (p ∨ q) ∨ r ↔ (q ∨ p) ∨ r := by
-- proof
  -- Use the commutativity of OR (or_comm) to swap p and q in the first disjunct.
  simp [or_comm]


-- created on 2025-04-09
