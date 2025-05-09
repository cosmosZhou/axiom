import Axiom.Set.Mem_Ioc.of.Lt.Le
import Axiom.Algebra.LtAddS.of.Lt
import Axiom.Algebra.LeAddS.of.Le
open Set Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {a b : α}
-- given
  (h : x ∈ Ioc a b)
  (d : α) :
-- imply
  x + d ∈ Ioc (a + d) (b + d) := by
-- proof
  have h_Lt := LtAddS.of.Lt h.left d
  have h_Le := LeAddS.of.Le h.right d
  apply Mem_Ioc.of.Lt.Le <;> assumption


-- created on 2025-03-02
-- updated on 2025-04-30
