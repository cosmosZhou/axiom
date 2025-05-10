import sympy.core.power
import Lemma.Basic


@[main]
private lemma main
  [LinearOrderedRing α]
  {a b : α}
-- given
  (h : |a| ≤ |b|) :
-- imply
  a² ≤ b² := by
-- proof
  -- Use the lemma `sq_le_sq` which states that if `a ≤ b` and `0 ≤ a`, then `a^2 ≤ b^2`.
  apply sq_le_sq.mpr h


-- created on 2025-04-06
-- updated on 2025-04-11
