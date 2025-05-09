import Axiom.Algebra.FMod.eq.Sub_MulFDiv
import Axiom.Logic.Ne.of.NotEq
open Algebra Logic


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : ∃ k : ℤ, n = k * d) :
-- imply
  n.fmod d = 0 := by
-- proof
  let ⟨k, h⟩ := h
  rw [h]
  rw [FMod.eq.Sub_MulFDiv]
  by_cases h : d = 0
  ·
    simp_all [h]
  ·
    have := Ne.of.NotEq h
    have := Int.mul_fdiv_cancel k this
    simp_all [this]


-- created on 2025-03-30
