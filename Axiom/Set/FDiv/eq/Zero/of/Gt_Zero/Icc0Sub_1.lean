import Axiom.Algebra.GeCoeS.of.Ge
import Axiom.Algebra.FDiv.eq.FloorDiv
import Axiom.Algebra.EqFloor.is.Le.et.Lt
import Axiom.Set.Ge.of.Mem_Icc
import Axiom.Algebra.Div.ge.Zero.of.Ge_0.Gt_0
import Axiom.Algebra.GtCoeS.of.Gt
import Axiom.Set.Le.of.Mem_Icc
import Axiom.Algebra.Lt_Add_1.of.Le
import Axiom.Algebra.LtDiv.of.Lt.Gt_0
open Algebra Set


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h₀ : d > 0)
  (h₁ : n ∈ Icc 0 (d - 1)) :
-- imply
  n // d = 0 := by
-- proof
  rw [FDiv.eq.FloorDiv]
  rw [EqFloor.is.Le.et.Lt]
  constructor
  ·
    apply Div.ge.Zero.of.Ge_0.Gt_0
    have := Ge.of.Mem_Icc h₁
    exact GeCoeS.of.Ge.int this
    exact GtCoeS.of.Gt.int h₀
  ·
    norm_num
    apply LtDiv.of.Lt.Gt_0
    ·
      norm_num
      have := Le.of.Mem_Icc h₁
      have := Lt_Add_1.of.Le this
      simp at this
      assumption
    ·
      exact GtCoeS.of.Gt.int h₀


-- created on 2025-03-30
-- updated on 2025-04-26
