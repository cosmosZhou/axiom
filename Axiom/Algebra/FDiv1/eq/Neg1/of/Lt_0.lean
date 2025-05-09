import Axiom.Algebra.FDiv.eq.FloorDiv
import Axiom.Algebra.LtCoeS.of.Lt
import Axiom.Algebra.EqFloor.of.Le.et.Lt
import Axiom.Algebra.DivInt.eq.Div
import Axiom.Algebra.GeDiv.of.Le_Mul.Lt_0
import Axiom.Algebra.Le_Sub_1.of.Lt
open Algebra


@[main]
private lemma main
  {d : ℤ}
-- given
  (h : d < 0) :
-- imply
  1 // d = -1 := by
-- proof
  have := LtCoeS.of.Lt.int (R := ℚ) h
  rw [FDiv.eq.FloorDiv]
  apply EqFloor.of.Le.et.Lt
  ·
    norm_cast
    simp
    rw [DivInt.eq.Div]
    apply GeDiv.of.Le_Mul.Lt_0
    ·
      simp
      norm_cast
      have := Le_Sub_1.of.Lt h
      simp at this
      linarith
    ·
      assumption
  ·
    simp
    norm_cast


-- created on 2025-03-30
-- updated on 2025-04-26
