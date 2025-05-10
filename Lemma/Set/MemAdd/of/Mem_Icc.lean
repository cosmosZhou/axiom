import Lemma.Set.Ge.Le.of.Mem_Icc
import Lemma.Algebra.GeAddS.of.Ge
import Lemma.Algebra.LeAddS.of.Le
import Lemma.Set.Mem_Icc.of.Le.Ge
open Set Algebra


@[main]
private lemma main
  [Preorder α]
  [Add α]
  [AddLeftMono α]
  [AddRightMono α]
  {x a b t : α}
-- given
  (h : x ∈ Icc a b) :
-- imply
  x + t ∈ Icc (a + t) (b + t) := by
-- proof
  let ⟨h₀, h₁⟩ := Ge.Le.of.Mem_Icc h
  have h₀ := GeAddS.of.Ge h₀ t
  have h₁ := LeAddS.of.Le h₁ t
  apply Mem_Icc.of.Le.Ge h₁ h₀


-- created on 2025-04-30
