import Axiom.Algebra.LtDivS.of.Lt.Gt_0
import Axiom.Set.Gt.of.Mem_Ioo
import Axiom.Algebra.GtDivS.of.Gt.Gt_0
import Axiom.Set.Lt.of.Mem_Ioo
import Axiom.Set.Mem_Ioo.of.Lt.Lt
open Set Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {a b : α}
-- given
  (h₀ : x ∈ Ioo a b)
  (h₁ : d > 0) :
-- imply
  x / d ∈ Ioo (a / d) (b / d) := by
-- proof
  have h_Gt := Gt.of.Mem_Ioo h₀
  have h_Gt := GtDivS.of.Gt.Gt_0 h_Gt h₁
  have h_Lt := Lt.of.Mem_Ioo h₀
  have h_Lt := LtDivS.of.Lt.Gt_0 h_Lt h₁
  apply Mem_Ioo.of.Lt.Lt <;> assumption


-- created on 2025-03-02
