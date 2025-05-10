import Lemma.Trigonometry.Arg.eq.Ite__Ite_Arcsin
import Lemma.Logic.Cond_Ite.is.OrAndS
import Lemma.Logic.Cond_Ite.is.AndImpS
import Lemma.Logic.ImpEq.is.ImpEq.subs
import Lemma.Logic.NotEq.is.Ne
import Lemma.Trigonometry.Arg.eq.Ite__Ite_Arccos.of.Ne_0
open Logic Trigonometry


@[main]
private lemma main
  {z : ℂ} :
-- imply
  arg z =
    if z = 0 then
      0
    else if im z ≥ 0 then
      arccos (re z / ‖z‖)
    else
      -arccos (re z / ‖z‖) := by
-- proof
  rw [Cond_Ite.is.AndImpS (R := Eq)]
  constructor
  rw [ImpEq.is.ImpEq.subs (p := fun z => arg z = 0)]
  simp
  rw [NotEq.is.Ne]
  intro h_ne
  apply Arg.eq.Ite__Ite_Arccos.of.Ne_0 h_ne


-- created on 2025-01-05
