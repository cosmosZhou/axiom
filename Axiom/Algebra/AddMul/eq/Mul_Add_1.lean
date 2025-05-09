import Axiom.Algebra.Mul_Add.eq.AddMulS
open Algebra


@[main]
private lemma main
  [Semiring α]
  {k d : α} :
-- imply
  d * k + d = d * (k + 1) := by
-- proof
  rw [Mul_Add.eq.AddMulS]
  simp


-- created on 2025-05-06
