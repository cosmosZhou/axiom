import stdlib.List.Vector
import Lemma.Logic.All_EqFunS.of.All_Eq
open Logic


@[main]
private lemma main
  {s : List α}
-- given
  (h : s is constant)
  (f : α → β) :
-- imply
  (s.map f) is constant := by
-- proof
  induction s with
  | nil =>
    simp [IsConstant.is_constant]
  | cons =>
    simp [IsConstant.is_constant]
    exact All_EqFunS.of.All_Eq.list h


-- created on 2024-07-01
-- updated on 2025-02-23
