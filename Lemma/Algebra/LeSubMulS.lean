import Lemma.Algebra.AddMul.le.Mul
import Lemma.Algebra.Le_Sub.of.LeAdd
import Lemma.Algebra.Add.comm
import Lemma.Algebra.Mul.comm
open Algebra


@[main]
private lemma left
  {m n : ℕ}
  {i : Fin n} :
-- imply
  m ≤ m * n - m * i := by
-- proof
  have := AddMul.le.Mul (n := n) (m := m) (i := i)
  apply Le_Sub.of.LeAdd.nat
  rw [Add.comm]
  assumption


@[main]
private lemma main
  {m n : ℕ}
  {i : Fin n} :
-- imply
  m ≤ n * m - i * m := by
-- proof
  have := AddMul.le.Mul (n := n) (m := m) (i := i)
  apply Le_Sub.of.LeAdd.nat
  rw [Add.comm]
  rw [Mul.comm]
  rw [Mul.comm (b := m)]
  assumption


-- created on 2025-05-06
-- updated on 2025-05-07
