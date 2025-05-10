import Lemma.Algebra.LeSubMulS
open Algebra


@[main]
private lemma left
  {m n : ℕ}
  {i : Fin n} :
-- imply
  min m (m * n - m * i) = m := by
-- proof
  have := LeSubMulS.left (n := n) (m := m) (i := i)
  simp [this]


@[main]
private lemma main
  {m n : ℕ}
  {i : Fin n} :
-- imply
  min m (n * m - i * m) = m := by
-- proof
  have := LeSubMulS (n := n) (m := m) (i := i)
  simp [this]


-- created on 2025-05-07
