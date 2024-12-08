import Axiom.sympy.core.containers.list

namespace Algebra.IsConstant.to

theorem All_Eq_HeadD
  {s : List α}
-- given
  (h: s is constant)
  (default: α) :
-- imply
  ∀ x ∈ s, x = s.headD default := by
-- proof
  match s with
  | List.nil => simp [IsConstant.is_constant] at *
  | List.cons x xs =>
    simp [IsConstant.is_constant] at *
    intro x x_in_s
    exact h x x_in_s


end Algebra.IsConstant.to

-- created on 2024-07-01
