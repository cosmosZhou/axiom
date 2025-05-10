import sympy.core.relational
import Lemma.Algebra.Le.et.Lt.of.EqFloor
import Lemma.Set.Mem_Ico.of.Le.Lt
open Algebra Set


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {x : α} :
-- imply
  x ∈ Ico (  ⌊x⌋ : α) (⌊x⌋ + 1) := by
-- proof
  denote h_d : d = ⌊x⌋
  have := Le.et.Lt.of.EqFloor h_d.symm
  let ⟨h₀, h₁⟩ := this
  rw [h_d] at h₀
  rw [h_d] at h₁
  apply Mem_Ico.of.Le.Lt h₀ h₁


-- created on 2025-03-30
-- updated on 2025-05-04
