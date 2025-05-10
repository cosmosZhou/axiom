import Lemma.Algebra.MulAdd.eq.AddMulS
open Algebra


@[main]
private lemma main
  [Semiring α]
  {k d : α} :
-- imply
  d + k * d = (1 + k) * d := by
-- proof
  rw [MulAdd.eq.AddMulS]
  simp


-- created on 2025-05-08
