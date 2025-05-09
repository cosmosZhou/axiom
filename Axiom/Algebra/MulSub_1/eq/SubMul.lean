import Axiom.Algebra.MulSub.eq.SubMulS
open Algebra


@[main]
private lemma nat
  {x a : ℕ} :
-- imply
  (a - 1) * x = a * x - x := by
-- proof
  rw [MulSub.eq.SubMulS.nat]
  simp


@[main]
private lemma main
  [Ring α]
  {x a : α} :
-- imply
  (a - 1) * x = a * x - x := by
-- proof
  rw [MulSub.eq.SubMulS]
  simp


-- created on 2025-03-31
