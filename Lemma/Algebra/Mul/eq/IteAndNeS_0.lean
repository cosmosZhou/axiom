import Lemma.Logic.NotAnd.is.OrNotS
import Lemma.Logic.Eq.of.NotNe
open Logic


@[main]
private lemma main
  [LinearOrderedRing α]
  -- [CommRing α] [DecidableEq α]
  {x y : α} :
-- imply
  x * y = if x ≠ 0 ∧ y ≠ 0 then
    x * y
  else
    0 := by
-- proof
  -- Use case analysis on the truth value of the condition `x ≠ 0 ∧ y ≠ 0`
  split_ifs with h
  ·
    -- If `h` is true, the `if` branch is taken, and we need to show `x * y = x * y`, which is trivially true.
    simp_all [mul_comm]
  ·
    -- If `h` is false, the `else` branch is taken, and we need to show `x * y = 0`.
    rw [NotAnd.is.OrNotS] at h
    cases' h with h h <;>
    ·
      have h := Eq.of.NotNe h
      rw [h]
      simp


-- created on 2025-04-18
