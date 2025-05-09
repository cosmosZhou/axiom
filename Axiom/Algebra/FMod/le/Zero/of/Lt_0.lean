import Axiom.Algebra.FMod.eq.Sub_MulFDiv
import Axiom.Algebra.Sub.le.Zero.of.Le
import Axiom.Algebra.GeMulFDiv.of.Lt_0
open Algebra


@[main]
private lemma main
  {d : ℤ}
-- given
  (h : d < 0)
  (n : ℤ) :
-- imply
  n.fmod d ≤ 0 := by
-- proof
  have := FMod.eq.Sub_MulFDiv (n := n) (d := d)
  rw [this]
  apply Sub.le.Zero.of.Le
  apply GeMulFDiv.of.Lt_0 h


-- created on 2025-03-21
