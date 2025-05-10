import Lemma.Set.Mem_Icc.of.Le.Le
import Lemma.Set.Ge.of.Mem_Icc
import Lemma.Set.Le.of.Mem_Icc
import Lemma.Algebra.GeDivS.of.Ge.Ge_0
import Lemma.Algebra.LeDivS.of.Le.Ge_0
open Set Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {a b : α}
-- given
  (h₀ : x ∈ Icc a b)
  (h₁ : d ≥ 0) :
-- imply
  x / d ∈ Icc (a / d) (b / d) := by
-- proof
  have h_Ge := Ge.of.Mem_Icc h₀
  have h_Ge := GeDivS.of.Ge.Ge_0 h_Ge h₁
  have h_Le := Le.of.Mem_Icc h₀
  have h_Ge := LeDivS.of.Le.Ge_0 h_Le h₁
  apply Mem_Icc.of.Le.Le <;> assumption


-- created on 2025-03-01
