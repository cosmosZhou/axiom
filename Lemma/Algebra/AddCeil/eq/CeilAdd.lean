import Lemma.Algebra.CeilAdd.eq.AddCeil
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {x : α}
  {d : ℤ} :
-- imply
  ⌈x⌉ + d = ⌈x + d⌉ := by
-- proof
  simp [CeilAdd.eq.AddCeil]


-- created on 2025-03-04
