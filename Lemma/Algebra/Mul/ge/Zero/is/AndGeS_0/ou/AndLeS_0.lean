import Lemma.Basic


@[main]
private lemma main
  [Semiring α]
  [LinearOrder α]
  [ExistsAddOfLE α]
  [MulPosStrictMono α]
  [PosMulStrictMono α]
  [AddLeftReflectLE α]
  [AddLeftMono α]
  {a b : α} :
-- imply
  a * b ≥ 0 ↔ a ≥ 0 ∧ b ≥ 0 ∨ a ≤ 0 ∧ b ≤ 0 := by
-- proof
  apply mul_nonneg_iff


-- created on 2025-03-23
