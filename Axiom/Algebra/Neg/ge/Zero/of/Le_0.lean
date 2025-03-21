import Axiom.Algebra.LeSubS.of.Le
import Axiom.Algebra.Sub.eq.Zero
import Axiom.Algebra.Sub0.eq.Neg
open Algebra


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {a : α}
-- given
  (h : a ≤ 0) :
-- imply
  -a ≥ 0 := by
-- proof
  have h := LeSubS.of.Le h a
  simp only [Sub.eq.Zero, Sub0.eq.Neg] at h
  exact h


-- created on 2024-11-29
