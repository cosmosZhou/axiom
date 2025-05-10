import Lemma.Algebra.FDiv.eq.FloorDiv
import Lemma.Algebra.EqFloor.is.Le.et.Lt
import Lemma.Algebra.Div.ge.Zero.of.Le_0.Lt_0
import Lemma.Set.Le.of.Mem_Icc
import Lemma.Algebra.LeCoeS.of.Le
import Lemma.Algebra.LtCoeS.of.Lt
import Lemma.Algebra.LtDiv.of.Gt.Lt_0
import Lemma.Set.Ge.of.Mem_Icc
import Lemma.Algebra.Gt.of.Ge_Add_1
open Algebra Set


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h₀ : d < 0)
  (h₁ : n ∈ Icc (d + 1) 0) :
-- imply
  n // d = 0 := by
-- proof
  rw [FDiv.eq.FloorDiv]
  rw [EqFloor.is.Le.et.Lt]
  constructor
  ·
    apply Div.ge.Zero.of.Le_0.Lt_0
    ·
      have := Le.of.Mem_Icc h₁
      exact LeCoeS.of.Le.int this
    ·
      exact LtCoeS.of.Lt.int h₀
  ·
    norm_num
    apply LtDiv.of.Gt.Lt_0
    ·
      norm_num
      have := Ge.of.Mem_Icc h₁
      exact Gt.of.Ge_Add_1 this
    ·
      exact LtCoeS.of.Lt.int h₀


-- created on 2025-03-30
-- updated on 2025-04-26
