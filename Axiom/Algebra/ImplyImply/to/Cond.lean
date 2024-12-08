import Axiom.Algebra.NotImply.to.And_Not
import Axiom.Algebra.Imply.to.ImplyNotS
import Axiom.Algebra.AndNot.to.False
namespace Algebra.ImplyImply.to

theorem Cond
  {p q : Prop}
-- given
  (h : (p → q) → p) :
-- imply
  p := by
-- proof
  by_contra hq
  have h' := Imply.to.ImplyNotS h
  have h' := NotImply.to.And_Not (h' hq)
  apply AndNot.to.False (And.intro hq h'.left)


end Algebra.ImplyImply.to

-- created on 2024-07-01
