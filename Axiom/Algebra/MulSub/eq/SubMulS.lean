import Axiom.Algebra.Sub.eq.Add_Neg
import Axiom.Algebra.NegMul.eq.MulNeg
import Axiom.Algebra.AddMulS.eq.MulAdd
open Algebra


@[main]
private lemma nat
  {x a b : ℕ} :
-- imply
  (a - b) * x = a * x - b * x := by
-- proof
  rw [Nat.sub_mul]


@[main]
private lemma main
  [Ring α]
  {x a b : α} :
-- imply
  (a - b) * x = a * x - b * x := by
-- proof
  rw [Sub.eq.Add_Neg (a := a)]
  rw [← AddMulS.eq.MulAdd]
  rw [Sub.eq.Add_Neg]
  rw [NegMul.eq.MulNeg]


-- created on 2024-11-26
-- updated on 2025-03-31
