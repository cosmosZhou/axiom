import Axiom.Algebra.Norm.eq.Abs
import Axiom.Algebra.Norm.ge.Zero
open Algebra


@[main]
private lemma main
  {a : ℂ} :
-- imply
  abs a ≥ 0 := by
-- proof
  rw [← Norm.eq.Abs]
  apply Norm.ge.Zero


-- created on 2025-01-15
