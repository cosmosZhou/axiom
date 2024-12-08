import Axiom.Algebra.IsConstant.to.All_Eq_HeadD
import Axiom.Algebra.IsConstant.to.IsConstantTail
import Axiom.Sets.In_Cons
import Axiom.Algebra.Ne_.Length.Zero.All_Fun.to.FunGet_0

namespace Algebra.IsConstant.to

theorem Eq_Replicate_HeadD
  {s : List α}
-- given
  (h: s is constant)
  (default : α) :
-- imply
  s = List.replicate s.length (s.headD default) := by
-- proof
  induction s with
  | nil =>
    simp
  | cons x xs ih =>
    have h_tail_is_constant : (xs is constant) := by
      apply IsConstant.to.IsConstantTail h

    have h_eq : xs = List.replicate xs.length (xs.headD default) := ih h_tail_is_constant

    simp
    unfold List.replicate
    simp [IsConstant.is_constant] at h

    have h_eq' : List.replicate xs.length (xs.headD default) =
      List.replicate xs.length x := by
      cases xs with
      | nil =>
        simp
      | cons y ys =>
        simp
        apply Ne_.Length.Zero.All_Fun.to.FunGet_0 (h_all := h)
        simp

    rw [h_eq'.symm, h_eq.symm]

end Algebra.IsConstant.to

-- created on 2024-07-01
