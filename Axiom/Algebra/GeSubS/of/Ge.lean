import Axiom.Algebra.LeSubS.of.Le
open Algebra


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {x y : α}
-- given
  (h : x ≥ y)
  (z : α) :
-- imply
  x - z ≥ y - z :=
-- proof
  LeSubS.of.Le h z


-- created on 2024-07-01
