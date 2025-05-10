import Lemma.Basic


@[main]
private lemma main
  [Ring α]
  [LinearOrder α]
  [PosMulStrictMono α]
  [MulPosStrictMono α]
  [AddLeftReflectLT α]
  [AddLeftStrictMono α]
  {a b : α} :
-- imply
  a * b < 0 ↔ a < 0 ∧ b > 0 ∨ b < 0 ∧ a > 0 := by
-- proof
  rw [Or.comm]
  rw [And.comm]
  apply mul_neg_iff


-- created on 2025-03-30
