import Lemma.Algebra.FDiv.eq.Ite__Ite__Ite__Ite__Ite
import Lemma.Logic.Iff_True.of.Cond
import Lemma.Algebra.Ge.is.False.of.Lt
import Lemma.Algebra.Eq.is.False.of.Lt
import Lemma.Algebra.Gt.is.False.of.Lt
import Lemma.Algebra.AddNeg.eq.Sub
import Lemma.Algebra.GeMulSubEDiv.of.Lt_0
import Lemma.Algebra.Neg.ge.Zero.of.Le_0
import Lemma.Algebra.Le.of.NotGt
import Lemma.Algebra.LeMulEDiv.of.Ge_0
import Lemma.Algebra.GeNeg.of.Le_Neg
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
