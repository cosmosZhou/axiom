import Axiom.Algebra.Mod_2.eq.One.of.IsOdd
open Algebra


@[main]
private lemma main
  {n : ℤ}
-- given
  (h : n is odd) :
-- imply
  ∃ k, n = 2 * k + 1 := by
-- proof
  use (n - 1) / 2
  have := Mod_2.eq.One.of.IsOdd h
    
  omega


-- created on 2025-03-04
-- updated on 2025-03-05
