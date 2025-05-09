import Axiom.Algebra.MulSub_1.eq.SubMul
open Algebra


@[main]
private lemma nat
  {x a : ℕ} :
-- imply
  a * x - x = (a - 1) * x := by
-- proof
  rw [MulSub_1.eq.SubMul.nat]


@[main]
private lemma main
  [Ring α]
  {x a : α} :
-- imply
  a * x - x = (a - 1) * x := by
-- proof
  rw [MulSub_1.eq.SubMul]


-- created on 2025-03-31
