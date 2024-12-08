import Axiom.sympy.core.containers.list
import Axiom.Algebra.All_Eq.to.All_EqFunS
import Axiom.Algebra.TailCons.eq.Tail

namespace Algebra.All_Eq.to

theorem IsConstant
  {s : List α}
  {x0 : α}
-- given
  (h: ∀ x ∈ s, x = x0) :
-- imply
  s is constant := by
-- proof
  match s with
  | List.nil => simp [IsConstant.is_constant] at *
  | List.cons x s =>
    simp [IsConstant.is_constant] at *
    intro t t_in_s
    have h1 : x = x0 := h.left
    have h2 : ∀ a ∈ s, a = x0 := h.right
  -- Use the universal quantifier to get `t = x0`
    have h3 : t = x0 := h2 t t_in_s
    rw [h1, h3]


end Algebra.All_Eq.to

-- created on 2024-07-01
