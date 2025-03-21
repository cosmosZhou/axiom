import Axiom.Basic
open Algebra


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d > 0) :
-- imply
  n % d < d := by
-- proof
  exact Int.emod_lt_of_pos n h


-- created on 2025-03-20
