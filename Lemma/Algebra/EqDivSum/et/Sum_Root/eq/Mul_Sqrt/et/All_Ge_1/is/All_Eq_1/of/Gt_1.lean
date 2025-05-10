import sympy.sets.sets
import Lemma.Algebra.All_Eq_1.of.All_Ge_1.Sum_Root.eq.Mul_Root_2.EqDivSum.Gt_1
import Lemma.Algebra.Sum.eq.Mul.of.All_Eq
import Lemma.Algebra.EqDivS.of.Eq
import Lemma.Algebra.Div.eq.One.of.Gt_0
import Lemma.Algebra.GtCoeS.of.Gt
import Lemma.Algebra.Gt.of.Gt.Gt
import Lemma.Algebra.All_Eq.of.All_Eq.Eq.is_constant
import Lemma.Algebra.All_Eq.of.All_Eq.Eq
import Lemma.Algebra.All_Eq.of.All_Eq.Lt.is_constant
import Lemma.Algebra.All_Eq.of.All_Eq.Lt
import Lemma.Algebra.Eq.of.All_Eq.Lt.is_constant
import Lemma.Algebra.Eq.of.All_Eq.Lt
import Lemma.Logic.All_EqFunS.of.All_Eq
import Lemma.Algebra.Pow1.eq.One
import Lemma.Algebra.Ge.of.Eq
import Lemma.Logic.All.of.All.All_Imp
open Algebra Logic


/--
This lemma establishes that for a sequence of real numbers indexed by natural numbers, the conditions of having the average of the first `n` terms equal to the `n`-th term, the sum of their roots matching a specific form, and all terms being at least one, are equivalent to all terms up to `n + 1` being exactly one.
It provides a characterization of constant sequences under these constraints, useful in verifying uniqueness and optimality in related problems.
-/
@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h : n > 1) :
-- imply
  ((∑ i ∈ range n, x i) / n = x n ∧ (∑ i ∈ range n, (x i) ^ (1 / (i + 2) : ℝ)) = n * (x n) ^ (1 / 2 : ℝ) ∧ ∀ i ∈ range n, x i ≥ 1) ↔ ∀ i ∈ range (n + 1), x i = 1 := by
-- proof
  have h_Gt_1 := GtCoeS.of.Gt.nat (R := ℝ) h
  have h_Gt_0 : (n : ℝ) > 0 := by apply Gt.of.Gt.Gt h_Gt_1 (by norm_num)
  constructor
  ·
    intro ⟨h₀, h₁, h₂⟩
    have h' := All_Eq_1.of.All_Ge_1.Sum_Root.eq.Mul_Root_2.EqDivSum.Gt_1 h h₀ h₁ h₂
    have := Sum.eq.Mul.of.All_Eq h'
    simp at this
    have := EqDivS.of.Eq this n
    simp [Div.eq.One.of.Gt_0 h_Gt_0] at this
    have h₀ := h₀.symm.trans this
    apply All_Eq.of.All_Eq.Eq.is_constant h₀ h'
  ·
    intro h'
    have h_Lt : n < n + 1 := by norm_num
    have h_All_Eq := All_Eq.of.All_Eq.Lt.is_constant h_Lt h'
    have h_Eq := Eq.of.All_Eq.Lt.is_constant h_Lt h'
    constructor
    ·
      have := Sum.eq.Mul.of.All_Eq h_All_Eq
      simp at this
      have := EqDivS.of.Eq this n
      simp [Div.eq.One.of.Gt_0 h_Gt_0] at this
      apply this.trans h_Eq.symm
    ·
      constructor
      ·
        rw [h_Eq]
        rw [Pow1.eq.One]
        let b := fun _ : ℕ => (1 : ℝ)
        let f := fun (x : ℝ) (i : ℕ) => x ^ (1 / (i + 2) : ℝ)
        have := All_EqFunS.of.All_Eq.binary (b := b) (f := f) h_All_Eq
        simp only [b, f] at this
        simp only [Pow1.eq.One] at this
        apply Sum.eq.Mul.of.All_Eq this
      ·
        have h_All : ∀ x : ℝ, x = 1 → x ≥ 1 := by
          intro i h_Eq
          apply Ge.of.Eq h_Eq
        apply All.of.All.All_Imp.finset h_All h_All_Eq


-- created on 2025-04-26
-- updated on 2025-04-27
