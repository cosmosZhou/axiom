import sympy.sets.sets
import Axiom.Algebra.Root_Add_2.lt.Sqrt.of.Gt_1.Gt_0
import Axiom.Logic.All_Not.of.NotAny
import Axiom.Logic.And_And.is.AndAnd
import Axiom.Algebra.Gt.of.Ge.Gt
import Axiom.Algebra.AllIco.of.AllRange
import Axiom.Logic.All_And.of.All.All
import Axiom.Algebra.Eq.of.Le.Ge
import Axiom.Logic.All.of.All.All_Imp
import Axiom.Algebra.All_LeRoot_Sqrt.of.All_Ge_1
import Axiom.Algebra.LtSumS.of.All_Le.Any_Lt
import Axiom.Algebra.Sum.eq.Add_Sum.of.Gt_0
import Axiom.Algebra.EqSumS.of.All_Eq
import Axiom.Algebra.Root_2.eq.Sqrt
import Axiom.Algebra.Add_Sub.eq.SubAdd
import Axiom.Algebra.CoeSub.eq.SubCoeS
import Axiom.Algebra.CoeSub.eq.SubCoeS.of.Ge
import Axiom.Algebra.Sum_Sqrt.le.Mul_Sqrt.of.EqDivSum.All_Ge_1.Ne_0
import Axiom.Algebra.Lt.of.Lt.Le
import Axiom.Algebra.Pow1.eq.One
import Axiom.Algebra.SubNatNat.eq.Sub
import Axiom.Algebra.SubAddSqrt.lt.Mul_SqrtDiv.of.Gt_1.Gt_1
import Axiom.Logic.All_EqFunS.of.All_Eq
import Axiom.Algebra.EqAdd0
open Algebra Logic


/--
Given a natural number `n > 1` and a sequence `x` of real numbers indexed by natural numbers, this lemma establishes an inequality involving sums of roots under the following conditions:
1. Each element `x i` for `i` in the range `[0, n-1]` is at least 1.
2. The first element `x 0` is strictly greater than 1.
3. The average of the first `n` elements of `x` equals the `n`-th element `x n`.
Under these conditions, the sum of each `x i` raised to the power `1/(i+2)` for `i` from 0 to `n-1` is strictly less than `n` times the square root of `x n`.
-/
@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n > 1)
  (h₁ : ∀ i ∈ range n, x i ≥ 1)
  (h₂ : x 0 > 1)
  (h₃ : (∑ i ∈ range n, x i) / n = x n) :
-- imply
  ∑ i ∈ range n, (x i) ^ (1 / (i + 2) : ℝ) < n * √(x n) := by
-- proof
  have h_All := All_LeRoot_Sqrt.of.All_Ge_1 h₁
  by_cases h : ∃ i ∈ Finset.Ico 1 n, x i > 1
  ·
    let ⟨i, hi⟩ := h
    let ⟨h_In, h_Gt_1⟩ := hi
    rw [Finset.mem_Ico] at h_In
    have h_Gt_0 := Gt.of.Ge.Gt h_In.left (by norm_num : 1 > 0)
    have h := Root_Add_2.lt.Sqrt.of.Gt_1.Gt_0 h_Gt_1 h_Gt_0
    have h_Any : ∃ i ∈ range n, (x i) ^ (1 / (i + 2) : ℝ) < √(x i) := by
      use i
      constructor
      ·
        rw [Finset.mem_range]
        exact h_In.right
      ·
        assumption
    have h_Lt := LtSumS.of.All_Le.Any_Lt h_All h_Any
    have := Sum_Sqrt.le.Mul_Sqrt.of.EqDivSum.All_Ge_1.Ne_0 (by linarith [h₀]) h₁ h₃
    exact Lt.of.Lt.Le h_Lt this
  ·
    have := All_Not.of.NotAny h
    simp [And_And.is.AndAnd] at this
    have h_All_Le_1 : ∀ i ∈ Finset.Ico 1 n, x i ≤ 1 := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      exact this i hi.left hi.right
    have h_All_Ge_1 := AllIco.of.AllRange h₁ 1
    have h_All_And := All_And.of.All.All h_All_Le_1 h_All_Ge_1
    have : ∀ t : ℝ, t ≤ 1 ∧ t ≥ 1 → t = 1 := by
      intro t ht
      exact Eq.of.Le.Ge ht.left ht.right
    have h_All_Eq := All.of.All.All_Imp this h_All_And
    let f := fun (xi : ℝ) (i : ℕ) => xi ^ (1 / (i + 2) : ℝ)
    have h_All_Eq_Root := All_EqFunS.of.All_Eq.binary (f := f) h_All_Eq
    simp only [f] at h_All_Eq_Root
    let f := fun i : ℕ => (x i) ^ (1 / (i + 2) : ℝ)
    have h_Eq_Sum := Sum.eq.Add_Sum.of.Gt_0 (x := f) (by linarith [h₀])
    simp only [f] at h_Eq_Sum
    simp only [EqAdd0.nat (R := ℝ)] at h_Eq_Sum
    rw [Root_2.eq.Sqrt] at h_Eq_Sum
    have h_Eq_Sum' := EqSumS.of.All_Eq h_All_Eq_Root
    simp only [Pow1.eq.One] at h_Eq_Sum'
    have h_Eq_Sub : ∑ x ∈ Finset.Ico 1 n, (1 : ℝ) = n - 1 := by
      norm_cast
      simp
      rw [SubNatNat.eq.Sub]
      rw [CoeSub.eq.SubCoeS.of.Ge (by linarith [h₀])]
    have h_Eq_Sum' := Eq.trans h_Eq_Sum' h_Eq_Sub
    rw [h_Eq_Sum'] at h_Eq_Sum
    norm_cast at h_Eq_Sum
    rw [SubNatNat.eq.Sub] at h_Eq_Sum
    rw [CoeSub.eq.SubCoeS.int] at h_Eq_Sum
    simp only [Add_Sub.eq.SubAdd] at h_Eq_Sum
    norm_cast
    norm_cast at h_Eq_Sum
    rw [h_Eq_Sum]
    have h_Eq_Sum_1 := EqSumS.of.All_Eq h_All_Eq
    have h_Eq_Sum := Sum.eq.Add_Sum.of.Gt_0 (x := x) (by linarith [h₀])
    rw [h_Eq_Sum_1] at h_Eq_Sum
    rw [h_Eq_Sub] at h_Eq_Sum
    rw [Add_Sub.eq.SubAdd] at h_Eq_Sum
    rw [h_Eq_Sum] at h₃
    rw [← h₃]
    apply SubAddSqrt.lt.Mul_SqrtDiv.of.Gt_1.Gt_1
    assumption
    assumption


-- created on 2025-04-06
-- updated on 2025-04-26
