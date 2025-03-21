import Axiom.Algebra.IsConstantMap.of.IsConstant
open Algebra


@[main]
private lemma main
  {s : Vector α n}
-- given
  (h: s is constant)
  (f : α → β) :
-- imply
  s.map f is constant := by
-- proof
  apply IsConstantMap.of.IsConstant h


-- created on 2024-07-01
