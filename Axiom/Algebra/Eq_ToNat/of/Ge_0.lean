import Axiom.Basic


@[main]
private lemma main
  {n : ℤ}
-- given
  (h : n ≥ 0) :
-- imply
  n = n.toNat := by
-- proof
  -- Apply the lemma `Int.toNat_of_nonneg` which states that if `n ≥ 0`, then `n.toNat = n`.
  rw [Int.toNat_of_nonneg h]


-- created on 2025-05-04
