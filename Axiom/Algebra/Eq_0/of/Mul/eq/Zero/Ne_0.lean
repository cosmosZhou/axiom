import Axiom.Logic.Ne.of.NotEq
import Axiom.Algebra.Mul.ne.Zero.of.Ne_0.Ne_0
open Algebra Logic


@[main]
private lemma main
  [LinearOrderedRing α]
  {a b : α}
-- given
  (h : a * b = 0)
  (h₀ : b ≠ 0) :
-- imply
  a = 0 := by
-- proof
  by_contra h
  have h := Ne.of.NotEq h
  have := Mul.ne.Zero.of.Ne_0.Ne_0 h h₀
  contradiction


-- created on 2025-03-30
-- updated on 2025-04-05
