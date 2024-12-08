import Axiom.Algebra.Eq.to.EqAddS.right

namespace Algebra.EqSub.to

theorem Eq_Add
  [AddGroup α]
  {x a b: α}
-- given
  (h : x - b = a) :
-- imply
  x = a + b := by
-- proof
  have h := Eq.to.EqAddS.right h b
  simp at h
  exact h


end Algebra.EqSub.to

-- created on 2024-07-01
