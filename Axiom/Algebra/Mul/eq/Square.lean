import Axiom.Algebra.Square.eq.Mul
open Algebra


@[main]
private lemma main
  [Monoid α]
  {x : α} :
-- imply
  x * x = x² := by
-- proof
  rw [Square.eq.Mul]


-- created on 2024-07-01
