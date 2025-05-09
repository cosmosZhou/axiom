import Axiom.Algebra.Le.of.NotGt
open Algebra


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : ¬a < b) :
-- imply
  a ≥ b :=
-- proof
  Le.of.NotGt h


-- created on 2025-03-23
