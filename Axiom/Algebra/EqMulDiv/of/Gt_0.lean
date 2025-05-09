import Axiom.Algebra.EqMulDiv.of.Ne_0
import Axiom.Algebra.Ne.of.Gt
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {b : α}
-- given
  (h : b > 0)
  (a : α) :
-- imply
  a / b * b = a := by
-- proof
  have h := Ne.of.Gt h
  apply EqMulDiv.of.Ne_0 h


-- created on 2025-05-04
