import sympy.functions.elementary.integers
import Lemma.Set.Mem_Range.of.Fract.eq.Zero
open Set


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {x : α}
-- given
  (h : x ∉ Set.range Int.cast) :
-- imply
  fract x ≠ 0 := by
-- proof
  by_contra h'
  have := Mem_Range.of.Fract.eq.Zero h'
  contradiction


-- created on 2025-04-04
