import Lemma.Algebra.Norm.eq.SqrtAddSqaureS
import Lemma.Algebra.EqSquareS.of.Eq
import Lemma.Algebra.AddSquareS.ge.Zero
import Lemma.Algebra.EqSquareSqrt.of.Ge_0
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
