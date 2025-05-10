import sympy.sets.sets
import Lemma.Algebra.All_Le.of.All_Le.All_Eq_Ite
import Lemma.Algebra.Sum.eq.Sum_Add_Sub.of.Mem_Range.All_Eq_Ite
import Lemma.Algebra.Sub.lt.Zero.of.Lt
import Lemma.Algebra.Lt.of.Eq_Add.Lt_0
import Lemma.Algebra.LeSumS.of.All_Le
import Lemma.Algebra.Lt.of.Le.Lt
open Algebra


@[main]
private lemma main
  {n : ℕ}
  {x y : ℕ → ℝ}
-- given
  (h₀ : ∀ i ∈ range n, x i ≤ y i)
  (h₁ : ∃ i ∈ range n, x i < y i) :
-- imply
  ∑ i ∈ range n, x i < ∑ i ∈ range n, y i := by
-- proof
  let ⟨i', h⟩ := h₁
  let ⟨h_In, h_Lt⟩ := h
  let y' := fun i => ite (i = i') (x i) (y i)
  have h_y' : ∀ i ∈ range n, y' i = ite (i = i') (x i) (y i) := by
    intro i hj
    by_cases h : i = i'
    ·
      rw [h]
    ·
      unfold y'
      simp [h]
  have := All_Le.of.All_Le.All_Eq_Ite h_In h₀ h_y'
  have h_Le := LeSumS.of.All_Le this
  have := Sum.eq.Sum_Add_Sub.of.Mem_Range.All_Eq_Ite h_In h_y'
  have h_Lt_0 := Sub.lt.Zero.of.Lt h_Lt
  have := Lt.of.Eq_Add.Lt_0 this h_Lt_0
  exact Lt.of.Le.Lt h_Le this


-- created on 2025-04-06
