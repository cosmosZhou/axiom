import Lemma.Algebra.EqLengthTake.of.Ge
import Lemma.Algebra.EqLengthReplicate
import Lemma.Algebra.ZipWithHMul.eq.Replicate_0.of.Eq_Length
import Lemma.Algebra.ZipWith.eq.ZipWith__Take.of.Le
open Algebra


@[main]
private lemma main
  [MulZeroClass α]
  {a : List α}
-- given
  (h : l ≤ a.length) :
-- imply
  List.zipWith HMul.hMul (List.replicate l 0) a = List.replicate l 0 := by
-- proof
  have h_Eq := EqLengthReplicate (0 : α) l
  rw [← h_Eq] at h
  have h₁ := ZipWith.eq.ZipWith__Take.of.Le (f := HMul.hMul) h
  rw [h_Eq] at h₁
  have h_Eq' := EqLengthTake.of.Ge h
  rw [h_Eq] at h_Eq'
  have h₂ := ZipWithHMul.eq.Replicate_0.of.Eq_Length h_Eq'.symm
  rw [h₂] at h₁
  assumption


-- created on 2025-05-02
