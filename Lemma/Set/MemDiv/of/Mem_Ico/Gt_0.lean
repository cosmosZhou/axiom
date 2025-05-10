import Lemma.Set.Ge.of.Mem_Ico
import Lemma.Algebra.GeDivS.of.Ge.Gt_0
import Lemma.Set.Lt.of.Mem_Ico
import Lemma.Algebra.LtDivS.of.Lt.Gt_0
import Lemma.Set.Mem_Ico.of.Le.Lt
open Set Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {a b : α}
-- given
  (h₀ : x ∈ Ico a b)
  (h₁ : d > 0) :
-- imply
  x / d ∈ Ico (a / d) (b / d) := by
-- proof
  have h_Ge := Ge.of.Mem_Ico h₀
  have h_Ge := GeDivS.of.Ge.Gt_0 h_Ge h₁
  have h_Lt := Lt.of.Mem_Ico h₀
  have h_Lt := LtDivS.of.Lt.Gt_0 h_Lt h₁
  apply Mem_Ico.of.Le.Lt <;> assumption


-- created on 2025-03-02
