import Lemma.Basic


@[main]
private lemma main
  (x : ℚ) :
-- imply
  |x - 3| = 4 + 2 * x ↔ x = -1 / 3 := by
-- proof
  rw [abs_eq_max_neg]
  constructor <;>
    intro h
  ·
    cases' max_eq_iff.mp h with h₀ h₁ <;>
      linarith
  ·
    rw [h]
    norm_num


-- created on 2025-03-31
-- updated on 2025-04-05
