import Axiom.Algebra.MulSub.eq.SubMulS
open Algebra


@[main]
private lemma nat
  {x a b : ℕ} :
-- imply
  a * x - b * x = (a - b) * x := by
-- proof
  rw [MulSub.eq.SubMulS.nat]


@[main]
private lemma main
  [Ring α]
  {x a b : α} :
-- imply
  a * x - b * x = (a - b) * x := by
-- proof
  rw [MulSub.eq.SubMulS]


-- created on 2024-07-01
-- updated on 2025-03-31
