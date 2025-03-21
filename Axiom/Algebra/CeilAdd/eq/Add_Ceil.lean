import Axiom.Algebra.Add.comm
import Axiom.Algebra.CeilAdd.eq.AddCeil
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {x : α}
  {d : ℤ} :
-- imply
  ⌈d + x⌉ = d + ⌈x⌉ := by
-- proof
  rw [Add.comm]
  rw [CeilAdd.eq.AddCeil]
  rw [Add.comm]


-- created on 2025-03-15
