import Axiom.Algebra.Neg.gt.Zero.of.Lt_0
import Axiom.Algebra.LtDivS.of.Lt.Gt_0
import Axiom.Algebra.Div_Neg.eq.NegDiv
import Axiom.Algebra.Gt.of.LtNegS
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {x a b : α}
-- given
  (h₀ : a < b)
  (h₁ : x < 0) :
-- imply
  a / x > b / x := by
-- proof
  have := Neg.gt.Zero.of.Lt_0 h₁
  have := LtDivS.of.Lt.Gt_0 h₀ this
  rw [Div_Neg.eq.NegDiv] at this
  rw [Div_Neg.eq.NegDiv] at this
  exact Gt.of.LtNegS this


-- created on 2025-03-20
