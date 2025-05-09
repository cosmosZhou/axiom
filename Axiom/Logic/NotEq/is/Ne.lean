import Axiom.Basic


@[main]
private lemma main
  {a b : α} :
-- imply
  (¬a = b) ↔ (a ≠ b) := by
-- proof
  constructor <;>
  ·
    intro h h_eq
    contradiction


-- created on 2025-01-12
