import Axiom.Algebra.FDiv.eq.Ite__Ite__Ite__Ite__Ite
import Axiom.Logic.Iff_True.of.Cond
import Axiom.Algebra.Ge.is.False.of.Lt
import Axiom.Algebra.Eq.is.False.of.Lt
import Axiom.Algebra.Gt.is.False.of.Lt
import Axiom.Algebra.AddNeg.eq.Sub
import Axiom.Algebra.GeMulSubEDiv.of.Lt_0
import Axiom.Algebra.Neg.ge.Zero.of.Le_0
import Axiom.Algebra.Le.of.NotGt
import Axiom.Algebra.LeMulEDiv.of.Ge_0
import Axiom.Algebra.GeNeg.of.Le_Neg
open Algebra Logic


@[main]
private lemma main
  {d : ℤ}
-- given
  (h : d < 0)
  (n : ℤ) :
-- imply
  n // d * d ≥ n := by
-- proof
  rw [FDiv.eq.Ite__Ite__Ite__Ite__Ite]
  have := Iff_True.of.Cond h
  simp [this]
  have := Ge.is.False.of.Lt h
  simp [this]
  have := Eq.is.False.of.Lt h
  simp [this]
  have := Gt.is.False.of.Lt h
  simp [this]
  split_ifs with h'
  ·
    rw [AddNeg.eq.Sub]
    apply GeMulSubEDiv.of.Lt_0 h
  ·
    have h := Le.of.NotGt h'
    have := Neg.ge.Zero.of.Le_0 h
    apply GeNeg.of.Le_Neg
    apply LeMulEDiv.of.Ge_0 this d


-- created on 2025-03-21
-- updated on 2025-03-29
