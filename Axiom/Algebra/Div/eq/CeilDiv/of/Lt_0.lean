import Axiom.Algebra.Div.eq.AddDiv___Mod
import Axiom.Algebra.EqCeil.equ.Lt.et.Le
import Axiom.Algebra.Div.gt.NegOne.of.Lt_0
import Axiom.Algebra.Gt_Add.of.Eq_Add.Gt
import Axiom.Algebra.Add_Neg.eq.Sub
import Axiom.Algebra.LeDivS.of.Lt_0
open Algebra


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d < 0) :
-- imply
  n / d = ⌈n / (d : ℚ)⌉ := by
-- proof
  apply Eq.symm
  rw [EqCeil.equ.Lt.et.Le]
  constructor
  have h_Eq := Div.eq.AddDiv___Mod (n := n) (d := d)
  have := Div.gt.NegOne.of.Lt_0 (n := n) h
  have := Gt_Add.of.Eq_Add.Gt h_Eq this
  rw [Add_Neg.eq.Sub] at this
  assumption
  exact LeDivS.of.Lt_0 h


-- created on 2025-03-20
