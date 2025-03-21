import Axiom.Algebra.Gt_Sub.of.GtAdd
open Algebra


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : c < a + b) :
-- imply
  c - b < a :=
-- proof
  Gt_Sub.of.GtAdd h


-- created on 2024-11-27
