import Axiom.Algebra.Re.eq.Zero.of.Eq_0
import Axiom.Algebra.Im.eq.Zero.of.Eq_0
import Axiom.Algebra.Eq_0.of.Re.eq.Zero.Im.eq.Zero
open Algebra


@[main]
private lemma main
  {z : ℂ} :
-- imply
  z = 0 ↔ re z = 0 ∧ im z = 0 := by
-- proof
  constructor
  intro h_Eq_0
  exact ⟨Re.eq.Zero.of.Eq_0 h_Eq_0, Im.eq.Zero.of.Eq_0 h_Eq_0⟩
  intro ⟨h_Re, h_Im⟩
  apply Eq_0.of.Re.eq.Zero.Im.eq.Zero <;> assumption


-- created on 2025-01-17
