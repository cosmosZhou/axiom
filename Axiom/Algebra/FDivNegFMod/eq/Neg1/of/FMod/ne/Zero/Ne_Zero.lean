import sympy.core.relational
import Axiom.Algebra.FDiv.eq.FloorDiv
import Axiom.Algebra.EqFloor.is.Le.et.Lt
import Axiom.Algebra.DivNeg.eq.NegDiv
import Axiom.Algebra.DivInt.eq.Div
import Axiom.Algebra.CoeNeg.eq.NegCoe
import Axiom.Algebra.LeNegS.of.Ge
import Axiom.Algebra.DivFMod.lt.One
import Axiom.Algebra.Neg.lt.Zero.of.Gt_0
import Axiom.Algebra.DivFMod.ge.Zero
import Axiom.Algebra.Gt.of.Ge.Ne
import Axiom.Algebra.Div.ne.Zero.of.Ne_0.Ne_0
import Axiom.Algebra.NeCoeS.of.Ne
import Axiom.Logic.Ne.of.NotEq
open Algebra Logic


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : n.fmod d ≠ 0)
  (h_d : d ≠ 0) :
-- imply
  (-(n.fmod d)) // d = -1 := by
-- proof
  denote h_r : r = n.fmod d
  rw [← h_r]
  rw [FDiv.eq.FloorDiv]
  norm_cast
  simp
  rw [EqFloor.is.Le.et.Lt]
  constructor
  ·
    norm_cast
    simp
    rw [DivInt.eq.Div]
    rw [CoeNeg.eq.NegCoe]
    rw [DivNeg.eq.NegDiv]
    apply LeNegS.of.Ge
    have := DivFMod.lt.One (n := n) (d := d)
    rw [← h_r] at this
    linarith
  ·
    norm_cast
    simp
    rw [DivInt.eq.Div]
    rw [CoeNeg.eq.NegCoe]
    rw [DivNeg.eq.NegDiv]
    apply Neg.lt.Zero.of.Gt_0
    have := DivFMod.ge.Zero (n := n) (d := d)
    rw [← h_r] at this
    apply Gt.of.Ge.Ne this
    rw [← h_r] at h
    apply Div.ne.Zero.of.Ne_0.Ne_0
    exact NeCoeS.of.Ne h
    have := Ne.of.NotEq h_d
    exact NeCoeS.of.Ne this


-- created on 2025-03-30
