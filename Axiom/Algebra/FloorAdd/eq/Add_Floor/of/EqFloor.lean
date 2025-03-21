import Axiom.Algebra.FloorAdd.eq.Add_Floor
open Algebra Real


@[main]
private lemma main
  [LinearOrderedField α]
  [FloorRing α]
  {x y : α}
-- given
  (h : ⌊x⌋ = x) :
-- imply
  ⌊x + y⌋ = x +   ⌊y⌋ := by
-- proof
  let d : ℤ := ⌊x⌋
  have h_Eq : d = ⌊x⌋ := rfl
  rw [← h_Eq] at h
  rw [← h]
  norm_cast
  apply FloorAdd.eq.Add_Floor


-- created on 2025-03-16
