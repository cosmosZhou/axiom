import Lemma.Logic.Imp.of.Iff
import Lemma.Logic.Bool.eq.MulBoolS.of.Imp
import Lemma.Algebra.Mul.comm
open Logic Algebra


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
-- given
  (h : p ↔ q) :
-- imply
  Bool.toNat p = Bool.toNat q := by
-- proof
  have := Imp.of.Iff h
  have h₀ := Bool.eq.MulBoolS.of.Imp this
  have := Imp.of.Iff h.symm
  have h₁ := Bool.eq.MulBoolS.of.Imp this
  rw [Mul.comm] at h₁
  exact Eq.trans h₀ h₁.symm


-- created on 2025-04-12
