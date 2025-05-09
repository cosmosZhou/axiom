import Axiom.Basic


@[main]
private lemma main
  {a b c : ℕ}
-- given
  (h : c ≤ b) :
-- imply
  a + b - c = a + (b - c) := by
-- proof
  
  rw [Nat.add_sub_assoc h]


-- created on 2025-03-31
