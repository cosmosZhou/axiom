import Axiom.Geometry.Arg.eq.Ite__Ite_Arcsin
import Axiom.Algebra.Eq_Ite.equ.OrAndS
import Axiom.Algebra.Eq_Ite.equ.AndImplyS_Eq
import Axiom.Algebra.ImplyEq.equ.ImplyEq.subs
import Axiom.Algebra.NotEq.equ.Ne
import Axiom.Geometry.Arg.eq.Ite__Ite_Arccos.of.Ne_0
open Geometry Algebra


@[main]
private lemma main
  {z : ℂ} :
-- imply
  arg z =
    if z = 0 then
      0
    else if im z ≥ 0 then
      arccos (re z / abs z)
    else
      -arccos (re z / abs z) := by
-- proof
  rw [Eq_Ite.equ.AndImplyS_Eq]
  constructor
  rw [ImplyEq.equ.ImplyEq.subs (p := fun z => arg z = 0)]
  simp
  rw [NotEq.equ.Ne]
  intro h_ne
  apply Arg.eq.Ite__Ite_Arccos.of.Ne_0 h_ne


-- created on 2025-01-05
