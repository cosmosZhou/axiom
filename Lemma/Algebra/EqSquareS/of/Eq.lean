import sympy.core.power
import Lemma.Basic


@[main]
private lemma main
  [Pow α Nat]
  {x y : α}
-- given
  (h : x = y) :
-- imply
  x² = y² := by
-- proof
  rw [h]


-- created on 2025-01-16
-- updated on 2025-01-17
