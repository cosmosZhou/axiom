import Axiom.Algebra.EqMulS.of.Eq
import Axiom.Algebra.MulAdd.eq.AddMulS
import Axiom.Algebra.MulPowS.eq.Pow_Add
import Axiom.Algebra.EqAddSub.of.Le
import Axiom.Algebra.ModEq.of.Eq
import Axiom.Algebra.ModEq_Pow2_1
import Axiom.Algebra.EqMul1
import Axiom.Algebra.ModEq.of.ModEq.ModEq__AddMul
import Axiom.Algebra.Eq_AddMulDiv___Mod
import Axiom.Algebra.Mul.comm
import Axiom.Algebra.MulMul.eq.Mul_Mul
open Algebra


@[main]
private lemma main
  {n m b : ℕ}
-- given
  (h : b ≤ m) :
-- imply
  n * 2 ^ b ≡ n / 2 ^ (m - b) + n % 2 ^ (m - b) * 2 ^ b [MOD 2 ^ m - 1] := by
-- proof
  have h_Eq_Add := Eq_AddMulDiv___Mod (n := n) (d := 2 ^ (m - b))
  have := EqMulS.of.Eq h_Eq_Add (2 ^ b)
  rw [MulAdd.eq.AddMulS] at this
  rw [MulMul.eq.Mul_Mul] at this
  rw [MulPowS.eq.Pow_Add] at this
  rw [EqAddSub.of.Le h] at this
  have := ModEq.of.Eq this (2 ^ m - 1)
  -- rw [Mul.comm (a := 2 ^ m)] at this
  have h_ModEq := ModEq_Pow2_1 (n := m)
  have := ModEq.of.ModEq.ModEq__AddMul h_ModEq this
  simp [EqMul1] at this
  assumption


-- created on 2025-03-15
-- updated on 2025-03-16
