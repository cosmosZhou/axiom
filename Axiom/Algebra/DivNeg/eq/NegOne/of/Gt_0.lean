import Axiom.Algebra.DivNeg.eq.NegOne.of.Ne_0
import Axiom.Algebra.Ne.of.Gt
open Algebra


@[main]
private lemma main
  [Preorder α]
  [Field α]
  {x : α}
-- given
  (h : x > 0) :
-- imply
  -x / x = -1 :=
-- proof
  (DivNeg.eq.NegOne.of.Ne_0 ∘ Ne.of.Gt) h


-- created on 2025-03-20
