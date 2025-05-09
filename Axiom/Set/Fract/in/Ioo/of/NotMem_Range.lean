import sympy.functions.elementary.integers
import sympy.sets.sets
import Axiom.Set.Fract.ne.Zero.of.NotMem
import Axiom.Set.Fract.in.Ico
import Axiom.Set.Mem_SDiff.of.Mem.Ne
import Axiom.Set.Ico.cut.Singleton.eq.Ioo
open Set


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {x : α}
-- given
  (h : x ∉ Set.range Int.cast) :
-- imply
  fract x ∈ Ioo 0 1 := by
-- proof
  have h := Fract.ne.Zero.of.NotMem h
  have := Fract.in.Ico (x := x)
  have := Mem_SDiff.of.Mem.Ne this h
  rw [Ico.cut.Singleton.eq.Ioo] at this
  assumption


-- created on 2025-04-04
