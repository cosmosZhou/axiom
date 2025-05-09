import Axiom.Algebra.Norm.eq.SqrtAddSqaureS
import Axiom.Algebra.EqSquareS.of.Eq
import Axiom.Algebra.AddSquareS.ge.Zero
import Axiom.Algebra.EqSquareSqrt.of.Ge_0
open Algebra


@[main]
private lemma main
  {z : ℂ} :
-- imply
  ‖z‖² = (re z)² + (im z)² := by
-- proof
  have := Norm.eq.SqrtAddSqaureS (z := z)
  have h := EqSquareS.of.Eq this
  have := AddSquareS.ge.Zero (a := re z) (b := im z)
  have := EqSquareSqrt.of.Ge_0 this
  exact this ▸ h


-- created on 2025-01-16
-- updated on 2025-01-17
