import Lemma.Set.Gt.of.Mem_Ioc
import Lemma.Algebra.GtDivS.of.Gt.Gt_0
import Lemma.Set.Le.of.Mem_Ioc
import Lemma.Algebra.LeDivS.of.Le.Gt_0
import Lemma.Set.Mem_Ioc.of.Lt.Le
open Set Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {a b : α}
-- given
  (h₀ : x ∈ Ioc a b)
  (h₁ : d > 0) :
-- imply
  x / d ∈ Ioc (a / d) (b / d) := by
-- proof
  have h_Gt := Gt.of.Mem_Ioc h₀
  have h_Gt := GtDivS.of.Gt.Gt_0 h_Gt h₁
  have h_Le := Le.of.Mem_Ioc h₀
  have h_Ge := LeDivS.of.Le.Gt_0 h_Le h₁
  apply Mem_Ioc.of.Lt.Le <;> assumption


-- created on 2025-03-01
-- updated on 2025-03-02
