import Axiom.Basic


@[main]
private lemma main
  {x y : ℕ}
-- given
  (h₀ : y > 0)
  (h₁ : x ≤ y) :
-- imply
  x - 1 < y := by
-- proof
  apply Nat.lt_of_le_sub_one h₀
  apply Nat.le_of_succ_le_succ
  simp
  rw [Nat.sub_add_cancel]
  assumption
  linarith


-- created on 2025-05-03
