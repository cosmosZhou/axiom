import Axiom.Algebra.Mul_Sub.eq.SubMulS
open Algebra


@[main]
private lemma nat
  {x b : ℕ} :
-- imply
  x - x * b = x * (1 - b) := by
-- proof
  rw [Mul_Sub.eq.SubMulS.nat]
  simp


@[main]
private lemma main
  [Ring α]
  {x b : α} :
-- imply
  x - x * b = x * (1 - b) := by
-- proof
  rw [Mul_Sub.eq.SubMulS]
  simp


-- created on 2025-04-20
