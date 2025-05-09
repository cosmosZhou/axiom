import Axiom.Algebra.GeMulS.of.Ge
import Axiom.Algebra.LeSubS.of.Le
open Algebra


@[main]
private lemma main
  {x y : ℕ}
-- given
  (h : x ≥ y)
  (k t : ℕ) :
-- imply
  k * x - t ≥ k * y - t := by
-- proof
  have := GeMulS.of.Ge h k
  apply LeSubS.of.Le.nat this


-- created on 2025-03-31
