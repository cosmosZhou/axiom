import Axiom.Algebra.Div.eq.One.of.Ne_0
import Axiom.Algebra.DivNeg.eq.NegDiv
import Axiom.Algebra.EqNegS.of.Eq
open Algebra


@[simp, main]
private lemma main
  [Field α]
  {a : α}
-- given
  (h : a ≠ 0) :
-- imply
  -a / a = -1 := by
-- proof
  rw [DivNeg.eq.NegDiv]
  have := Div.eq.One.of.Ne_0 h
  apply EqNegS.of.Eq this


-- created on 2025-03-20
