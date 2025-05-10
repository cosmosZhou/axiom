import Lemma.Algebra.Neg.gt.Zero.of.Lt_0
import Lemma.Algebra.GtDivS.of.Gt.Gt_0
import Lemma.Algebra.Div_Neg.eq.NegDiv
import Lemma.Algebra.Lt.of.GtNegS
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {x a b : α}
-- given
  (h₀ : a > b)
  (h₁ : x < 0) :
-- imply
  a / x < b / x := by
-- proof
  have h₁ := Neg.gt.Zero.of.Lt_0 h₁
  have := GtDivS.of.Gt.Gt_0 h₀ h₁
  rw [Div_Neg.eq.NegDiv] at this
  rw [Div_Neg.eq.NegDiv] at this
  apply Lt.of.GtNegS this


-- created on 2025-03-29
