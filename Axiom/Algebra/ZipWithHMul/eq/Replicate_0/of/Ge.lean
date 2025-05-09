import Axiom.Algebra.ZipWith.eq.ZipWith_Take.of.Ge
import Axiom.Algebra.EqLengthTake.of.Ge
import Axiom.Algebra.EqLengthReplicate
import Axiom.Algebra.ZipWithHMul.eq.Replicate_0.of.EqLength
open Algebra


@[main]
private lemma main
  [MulZeroClass α]
  {a : List α}
-- given
  (h : a.length ≥ l) :
-- imply
  List.zipWith HMul.hMul a (List.replicate l 0) = List.replicate l 0 := by
-- proof
  have h_Eq := EqLengthReplicate (0 : α) l
  rw [← h_Eq] at h
  have h₁ := ZipWith.eq.ZipWith_Take.of.Ge (f := HMul.hMul) h
  rw [h_Eq] at h₁
  have h_Eq' := EqLengthTake.of.Ge h
  rw [h_Eq] at h_Eq'
  have h₂ := ZipWithHMul.eq.Replicate_0.of.EqLength h_Eq'
  rw [h₂] at h₁
  assumption


-- created on 2025-05-02
