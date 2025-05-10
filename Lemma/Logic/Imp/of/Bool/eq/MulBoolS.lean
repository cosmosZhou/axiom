import sympy.core.logic
import Lemma.Algebra.EqCoeS.of.Eq
import Lemma.Algebra.Sub.eq.Zero.of.Eq
import Lemma.Algebra.CoeMul.eq.MulCoeS
import Lemma.Algebra.Sub_Mul.eq.Mul_Sub1
import Lemma.Algebra.OrEqS_0.of.Mul.eq.Zero
import Lemma.Algebra.Eq.of.Sub.eq.Zero
import Lemma.Algebra.Ne_1.of.Eq_0
import Lemma.Logic.Ne.is.NotEq
import Lemma.Logic.Imp.of.OrNot
import Lemma.Logic.Bool.eq.One.is.Cond
open Algebra Logic


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
-- given
  (h : Bool.toNat p = Bool.toNat p * Bool.toNat q) :
-- imply
  p → q := by
-- proof
  have := EqCoeS.of.Eq.nat (R := ℤ) h
  rw [CoeMul.eq.MulCoeS.nat] at this
  have := Sub.eq.Zero.of.Eq this
  rw [Sub_Mul.eq.Mul_Sub1] at this
  have := OrEqS_0.of.Mul.eq.Zero this
  mp [Eq.of.Sub.eq.Zero (a := (1 : ℤ)) (b := (Bool.toNat q : ℤ))] at this
  -- mp [Eq.of.Sub.eq.Zero] at this
  mp [Ne_1.of.Eq_0 (a := (Bool.toNat p : ℤ))] at this
  rw [Ne.is.NotEq] at this
  have := Imp.of.OrNot this
  norm_cast at this
  rw [Bool.eq.One.is.Cond] at this
  rw [Eq.comm] at this
  rw [Bool.eq.One.is.Cond] at this
  assumption


-- created on 2025-04-20
