import Axiom.Algebra.All_EqFunS.of.All_Eq
import Axiom.Algebra.TailCons.eq.Tail
import Axiom.Algebra.IsConstant.of.All_Eq
open Algebra


@[main]
private lemma main
  {s : List α}
-- given
  (h: s is constant) :
-- imply
  s.tail is constant := by
-- proof
  cases s with
  | nil =>
    simp [IsConstant.is_constant]
  | cons x0 X =>
    simp [IsConstant.is_constant] at h
    simp [TailCons.eq.Tail]
    apply IsConstant.of.All_Eq h


-- created on 2024-07-01
