import Lemma.Algebra.All_EqSumMap_FunMul__DotMapS
import Lemma.Algebra.AddMulS.eq.MulAdd
open Algebra


@[main]
private lemma main
  [Add β] [MulZeroClass β] [RightDistribClass β]
  {s : List α}
  {f : α → β}
  {const : β} :
-- imply
  (s.map fun x => f x * const).sum = (s.map f).sum * const := by
-- proof
  induction s with
  | nil =>
    -- Base case: s is the empty list
    simp [List.sum_nil]
  | cons a s ih =>
    -- Inductive case: s is a non-empty list
    simp [List.sum_cons, ih, AddMulS.eq.MulAdd]


-- created on 2024-07-01
