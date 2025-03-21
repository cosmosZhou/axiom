import Axiom.Algebra.All_EqSumMap_FunMul__DotMapS
import Axiom.Algebra.SumMap_FunMul.eq.MulSumMap


@[simp, main]
private lemma main
  [Add β] [Zero β]
  {s : Vector α n}
  {f : α → β} :
-- imply
  (s.val.map f).sum = (s.map f).sum := by
-- proof
  rfl


-- created on 2024-07-01
