import Lemma.Algebra.LtFMod.of.Gt_0
import Lemma.Algebra.LtDivS.of.Lt.Gt_0
import Lemma.Algebra.LtCoeS.of.Lt
import Lemma.Algebra.GtCoeS.of.Gt
import Lemma.Algebra.Div.eq.One.of.Gt_0
import Lemma.Algebra.GtFMod.of.Lt_0
import Lemma.Algebra.Le.of.NotGt
import Lemma.Algebra.Lt.of.Le.Ne
import Lemma.Algebra.LtDivS.of.Gt.Lt_0
import Lemma.Algebra.Div.eq.One.of.Lt_0
open Algebra


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  (n.fmod d) / (d : ℚ) < 1 := by
-- proof
  by_cases h : d > 0
  have := LtFMod.of.Gt_0 (n := n) h
  have := LtCoeS.of.Lt.int (R := ℚ) this
  have h' := GtCoeS.of.Gt.int (R := ℚ) h
  have := LtDivS.of.Lt.Gt_0 this h'
  rw [Div.eq.One.of.Gt_0 h'] at this
  assumption
  by_cases h' : d = 0
  rw [h']
  norm_num
  have h := Le.of.NotGt h
  have h := Lt.of.Le.Ne h h'
  have := GtFMod.of.Lt_0 (n := n) h
  have := GtCoeS.of.Gt.int (R := ℚ) this
  have h' := LtCoeS.of.Lt.int (R := ℚ) h
  have := LtDivS.of.Gt.Lt_0 this h'
  rw [Div.eq.One.of.Lt_0 h'] at this
  assumption


-- created on 2025-03-28
-- updated on 2025-03-30
