import Lemma.Algebra.All_Eq_HeadD.of.IsConstant
import Lemma.Algebra.IsConstantTail.of.IsConstant
import Lemma.Set.Expr.mem.Cons
import Lemma.Algebra.FunGet_0.of.NeLength_0.All_Fun
open Algebra


@[main]
private lemma main
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
    have h_tail_is_constant := IsConstantTail.of.IsConstant h
    have h_eq : xs = List.replicate xs.length (xs.headD default) := ih h_tail_is_constant
    simp
    unfold List.replicate
    simp [IsConstant.is_constant] at h
    have h_eq' : List.replicate xs.length (xs.headD default) = List.replicate xs.length x := by
      match xs with
      | .nil =>
        simp
      | .cons y ys =>
        simp
        apply FunGet_0.of.NeLength_0.All_Fun (h_all := h)
        simp
    rw [h_eq'.symm, h_eq.symm]


-- created on 2024-07-01
