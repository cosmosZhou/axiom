import Axiom.Algebra.Le_Sub.of.LeAdd
open Algebra


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : c ≥ a + b) :
-- imply
  c - b ≥ a :=
-- proof
  Le_Sub.of.LeAdd h


-- created on 2024-11-27
