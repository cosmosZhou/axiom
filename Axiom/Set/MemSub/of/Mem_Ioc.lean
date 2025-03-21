import Axiom.Set.MemAdd.of.Mem_Ioc
import Axiom.Algebra.Add_Neg.eq.Sub
open Set Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {a b : α}
-- given
  (h : x ∈ Ioc a b)
  (d : α) :
-- imply
  x - d ∈ Ioc (a - d) (b - d) := by
-- proof
  have := MemAdd.of.Mem_Ioc h (-d)
  simp only [Add_Neg.eq.Sub] at this
  assumption


-- created on 2025-03-02
