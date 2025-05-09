import Axiom.Trigonometry.Arg.eq.Ite__Ite_Arcsin
import Axiom.Logic.Cond_Ite.is.AndImpS
open Logic Trigonometry


@[main]
private lemma main
  {z : ℂ}
-- given
  (h : z ≠ 0) :
-- imply
  arg z =
    if im z ≥ 0 then
      arccos (re z / ‖z‖)
    else
      -arccos (re z / ‖z‖) := by
-- proof
  rw [Cond_Ite.is.AndImpS (R := Eq)]
  constructor
  by_cases h_GeRe_0 : re z ≥ 0
  intro h_GeIm_0
  -- rw [Arg.eq.Ite__Ite_Arcsin]
  sorry
  sorry
  sorry


-- created on 2025-01-12
-- updated on 2025-04-17
