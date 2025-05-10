import sympy.core.relational
import Lemma.Algebra.Pow2.eq.One.mod.SubPow2
import Lemma.Algebra.ModEq.of.Eq
import Lemma.Algebra.EqMul1
import Lemma.Algebra.ModEq.of.ModEq.ModEq__AddMul
import Lemma.Algebra.Eq_AddMulDiv___Mod
import Lemma.Algebra.Mul.comm
open Algebra


@[main]
private lemma main
  {n m : ℕ} :
-- imply
  n ≡ n / 2 ^ m + n % 2 ^ m [MOD 2 ^ m - 1] := by
-- proof
  have h_ModEq__1 := Pow2.eq.One.mod.SubPow2 (n := m)
  denote h_eq_k : k = 2 ^ m
  rw [← h_eq_k]
  rw [← h_eq_k] at h_ModEq__1
  have h_Eq_Add := Eq_AddMulDiv___Mod (n := n) (d := k)
  have h_ModEq := ModEq.of.Eq h_Eq_Add (k - 1)
  -- rw [Mul.comm] at h_ModEq
  have := ModEq.of.ModEq.ModEq__AddMul h_ModEq__1 h_ModEq
  simp [EqMul1] at this
  assumption


-- created on 2025-03-10
-- updated on 2025-03-16
