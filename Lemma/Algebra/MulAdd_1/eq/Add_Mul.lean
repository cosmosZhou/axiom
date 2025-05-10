import Lemma.Algebra.Add.comm
import Lemma.Algebra.MulAdd_1.eq.AddMul
open Algebra


@[main]
private lemma main
  [Semiring α]
  {k d : α} :
-- imply
  (k + 1) * d = d + k * d := by
-- proof
  rw [Add.comm (a := d)]
  apply MulAdd_1.eq.AddMul


-- created on 2025-05-08
