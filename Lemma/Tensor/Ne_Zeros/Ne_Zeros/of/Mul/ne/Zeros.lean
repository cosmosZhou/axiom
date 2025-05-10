import Lemma.Tensor.MulZeros.eq.Zeros
import Lemma.Tensor.Mul_Zeros.eq.Zeros
open Tensor


@[main]
private lemma main
  [MulZeroClass α]
  {a b : Tensor α s}
-- given
  (h : a * b ≠ Zeros s) :
-- imply
  a ≠ Zeros s ∧ b ≠ Zeros s := by
-- proof
  constructor
  ·
    -- Prove a ≠ Zeros s
    intro h_a
    rw [h_a] at h
    rw [MulZeros.eq.Zeros] at h
    contradiction
  ·
    -- Prove b ≠ Zeros s
    intro h_b
    rw [h_b] at h
    rw [Mul_Zeros.eq.Zeros] at h
    contradiction


-- created on 2025-05-02
