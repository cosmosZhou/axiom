import sympy.functions.elementary.integers
import Lemma.Set.Fract.ne.Zero.of.NotMem
import Lemma.Set.Fract.in.Ico
import Lemma.Set.Mem_SDiff.of.Mem.Ne
import Lemma.Set.Ico.cut.Singleton.eq.Ioo
open Set


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {x : α}
-- given
  (h : x ∉ Set.range Int.cast) :
-- imply
  fract x > 0 := by
-- proof
  have h := Fract.ne.Zero.of.NotMem h
  have := Fract.in.Ico (x := x)
  have h := Mem_SDiff.of.Mem.Ne this h
  have := Ico.cut.Singleton.eq.Ioo (a := (0 : α)) (b := 1)
  rw [this] at h
  exact h.left


-- created on 2025-04-04
