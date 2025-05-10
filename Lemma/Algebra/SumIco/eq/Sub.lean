import sympy.sets.sets
import Mathlib.Data.Finset.Interval
import Lemma.Basic


@[main]
private lemma main
  {a b : ℕ} :
-- imply
  ∑ _ ∈ Finset.Ico a b, 1 = b - a := by
-- proof
  -- Use the fact that the sum of 1's over a range is the number of elements in the range.
  rw [Finset.sum_const]
  -- Simplify the expression to show that the sum is equal to the number of elements in the interval [a, b).
  simp_all [Finset.card_Ico_finset, Nat.cast_sub]


-- created on 2025-04-06
