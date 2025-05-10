import Lemma.Algebra.LeAdd_1
import Lemma.Algebra.AddMul.eq.Mul_Add_1
import Lemma.Algebra.LeMulS.of.Ge_0.Le
open Algebra


@[main]
private lemma main
  {n : ℕ}
  {i : Fin n} :
-- imply
  m * i + m ≤ m * n := by
-- proof
  have := LeAdd_1 (n := n) (i := i)
  rw [AddMul.eq.Mul_Add_1]
  apply LeMulS.of.Ge_0.Le (by simp) this


-- created on 2025-05-06
