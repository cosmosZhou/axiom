import Axiom.Algebra.Imply.equ.OrNot

namespace Algebra.Cond.to

theorem Imply
  {p q : Prop}
-- given
  (h : p) :
-- imply
  q → p := by
-- proof
  simp [h]

end Algebra.Cond.to

-- created on 2024-07-01
