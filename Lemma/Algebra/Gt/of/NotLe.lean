import Lemma.Algebra.Lt.of.NotGe
open Algebra


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : ¬a ≤ b) :
-- imply
  a > b := by
-- proof
  apply Lt.of.NotGe h


-- created on 2025-03-29
