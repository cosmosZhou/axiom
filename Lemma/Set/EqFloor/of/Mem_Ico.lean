import Lemma.Algebra.EqFloor.of.Le.et.Lt
import Lemma.Set.Le.of.Mem_Ico
import Lemma.Set.Lt.of.Mem_Ico
open Algebra Set


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {z : ℤ}
  {x : α}
-- given
  (h : x ∈ Ico (z : α) (z + 1)) :
-- imply
  ⌊x⌋ = z := by
-- proof
  apply EqFloor.of.Le.et.Lt
  ·
    exact Le.of.Mem_Ico h
  ·
    exact Lt.of.Mem_Ico h


-- created on 2025-05-04
