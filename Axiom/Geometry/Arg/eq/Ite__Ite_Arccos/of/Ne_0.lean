import Axiom.Geometry.Arg.eq.Ite__Ite_Arcsin
import Axiom.Algebra.Eq_Ite.equ.OrAndS
import Axiom.Algebra.Eq_Ite.equ.AndImplyS_Eq
import Axiom.Algebra.ImplyEq.equ.ImplyEq.subs
import Axiom.Algebra.NotEq.equ.Ne
open Geometry Algebra


@[main]
private lemma main
  {z: ℂ}
  (h : z ≠ 0) :
-- imply
  arg z =
    if im z ≥ 0 then
      arccos (re z / abs z)
    else
      -arccos (re z / abs z) := by
-- proof
  rw [Eq_Ite.equ.AndImplyS_Eq]
  constructor
  by_cases h_GeRe_0 : re z ≥ 0
  intro h_GeIm_0
  -- rw [Arg.eq.Ite__Ite_Arcsin]
  sorry


-- created on 2025-01-12
