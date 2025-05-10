import Lemma.Set.Ge.Le.of.Mem_Icc
import Lemma.Set.Mem_Icc.of.Le.Ge
import Lemma.Algebra.GeSubS.of.Ge
import Lemma.Algebra.LeSubS.of.Le
open Set Algebra


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {x a b t : α}
-- given
  (h : x ∈ Icc a b) :
-- imply
  x - t ∈ Icc (a - t) (b - t) := by
-- proof
  let ⟨h₀, h₁⟩ := Ge.Le.of.Mem_Icc h
  have h₀ := GeSubS.of.Ge h₀ t
  have h₁ := LeSubS.of.Le h₁ t
  apply Mem_Icc.of.Le.Ge h₁ h₀


-- created on 2025-05-01
