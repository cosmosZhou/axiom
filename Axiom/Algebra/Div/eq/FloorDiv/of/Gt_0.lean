import Axiom.Algebra.Div.eq.AddDiv___Mod
import Axiom.Algebra.GeDivS.of.Gt_0
import Axiom.Algebra.Div.lt.One.of.Gt_0
import Axiom.Algebra.Lt_Add.of.Eq_Add.Lt
import Axiom.Algebra.EqFloor.equ.Le.et.Lt
open Algebra


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d > 0) :
-- imply
  n / d = ⌊n / (d : ℚ)⌋ := by
-- proof
  apply Eq.symm
  rw [EqFloor.equ.Le.et.Lt]
  constructor
  exact GeDivS.of.Gt_0 h
  have h_Eq := Div.eq.AddDiv___Mod (n := n) (d := d)
  have := Div.lt.One.of.Gt_0 (n := n) h
  exact Lt_Add.of.Eq_Add.Lt h_Eq this


-- created on 2025-03-17
-- updated on 2025-03-20
