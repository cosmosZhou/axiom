import Axiom.Algebra.GeMulS.of.Ge
import Axiom.Algebra.GeAddS.of.Ge
open Algebra


@[main]
private lemma main
  {x y k : ℕ}
-- given
  (h : x ≥ y)
  (t : ℕ) :
-- imply
  k * x + t ≥ k * y + t := by
-- proof
  have := GeMulS.of.Ge h k
  apply GeAddS.of.Ge this


-- created on 2025-03-31
