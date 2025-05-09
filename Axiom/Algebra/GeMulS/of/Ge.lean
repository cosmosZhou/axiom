import Axiom.Basic


@[main]
private lemma main
  {x y : ℕ}
-- given
  (h : x ≥ y)
  (k : ℕ) : 
-- imply
  k * x ≥ k * y := by
-- proof
  induction k with
  | zero =>
  -- Case 1: k = 0
  -- 0 * x = 0 and 0 * y = 0, so 0 ≥ 0, which is true.
    simp
  | succ k _ =>
  -- Case 2: k > 0
  -- Use the induction hypothesis and the fact that multiplication by k positive number preserves the order.
    simp_all [Nat.mul_succ]


-- created on 2025-03-31
