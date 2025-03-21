import Axiom.Algebra.Ge_Sub.of.GeAdd
open Algebra


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : c ≤ a + b) :
-- imply
  c - b ≤ a :=
-- proof
  Ge_Sub.of.GeAdd h


-- created on 2024-11-27
