import Axiom.Algebra.DivAdd.eq.AddDivS
import Axiom.Algebra.Div.eq.One.of.Ne_0
open Algebra


@[main]
private lemma main
  [Field α]
  {x d : α} 
  (h : d ≠ 0) :
-- imply
  (d + x) / d = 1 + x / d := by
-- proof
  rw [DivAdd.eq.AddDivS]
  rw [Div.eq.One.of.Ne_0 h]


-- created on 2025-03-25
