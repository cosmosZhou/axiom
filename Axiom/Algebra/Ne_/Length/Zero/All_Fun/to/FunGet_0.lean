import Axiom.Algebra.IsConstant.to.All_Eq_HeadD
import Axiom.Algebra.IsConstant.to.IsConstantTail
import Axiom.Sets.In_Cons
import Axiom.Algebra.Ne_0.to.Eq_Cons_Tail

namespace Algebra.Ne_.Length.Zero.All_Fun.to

theorem FunGet_0
  {s : List α}
  {p: α → Prop}
-- given
  (h_ne: s.length ≠ 0)
  (h_all : ∀ t ∈ s, p t) :
-- imply
  p s[0] := by
-- proof
  apply h_all s[0]
  have h_eq := Ne_0.to.Eq_Cons_Tail h_ne

  have h_in : s[0] ∈ s[0] :: s.tail := Sets.In_Cons

  rw [h_eq.symm] at h_in
  exact h_in


end Algebra.Ne_.Length.Zero.All_Fun.to

-- created on 2024-07-01
