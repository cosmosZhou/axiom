import Lemma.Algebra.LeCeil.of.Le
import Lemma.Algebra.Div.ge.Zero.of.Ge_0.Ge_0
import Lemma.Algebra.DivNeg.eq.NegDiv
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  [FloorRing α]
  {n d : ℕ} :
-- imply
  ⌈(-n : α) / d⌉.toNat = 0 := by
-- proof
  simp
  apply LeCeil.of.Le
  simp
  rw [DivNeg.eq.NegDiv]
  have h_Ge_n := Nat.cast_nonneg (α := α) n
  have h_Ge_d := Nat.cast_nonneg (α := α) d
  have := Div.ge.Zero.of.Ge_0.Ge_0 h_Ge_n h_Ge_d
  linarith [this]


-- created on 2025-05-05
