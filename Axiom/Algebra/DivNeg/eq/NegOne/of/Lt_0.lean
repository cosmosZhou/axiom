import Axiom.Algebra.Ne.of.Lt
import Axiom.Algebra.DivNeg.eq.NegOne.of.Ne_0
open Algebra


@[main]
private lemma main
  [Preorder α]
  [Field α]
  {x : α}
-- given
  (h : x < 0) :
-- imply
  -x / x = -1 :=
-- proof
  (DivNeg.eq.NegOne.of.Ne_0 ∘ Ne.of.Lt) h


-- created on 2025-03-20
