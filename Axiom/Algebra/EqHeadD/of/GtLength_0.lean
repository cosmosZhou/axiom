import Axiom.Algebra.Ne.of.Gt
import Axiom.Algebra.EqHeadD.of.NeLength_0
open Algebra


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length > 0)
  (default : α) :
-- imply
  s.headD default = s[0] := by
-- proof
  have := Ne.of.Gt h
  apply EqHeadD.of.NeLength_0 this


-- created on 2025-05-04
