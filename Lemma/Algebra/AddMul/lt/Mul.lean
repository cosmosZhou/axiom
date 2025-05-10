import stdlib.List.Vector
import Lemma.Algebra.LeSub_1
import Lemma.Algebra.LeMulS.of.Le.Ge_0
import Lemma.Algebra.LeAddS.of.Le.Le
import Lemma.Algebra.Lt.of.Le_Sub_1.Gt_0
import Lemma.Algebra.MulSub.eq.SubMulS
import Lemma.Algebra.Add_Sub.eq.SubAdd
import Lemma.Algebra.Add_Sub.eq.SubAdd.Ge
import Lemma.Algebra.EqAddSub.of.Le
open Algebra


@[main]
private lemma main
-- given
  (i : Fin m)
  (j : Fin n) :
-- imply
  i * n + j < m * n := by
-- proof
  have hi := LeSub_1 i
  have hin := LeMulS.of.Le.Ge_0 hi (show n ≥ 0 by simp)
  have hj := LeSub_1 j
  have h_Le := LeAddS.of.Le.Le hin hj
  rw [MulSub.eq.SubMulS.nat] at h_Le
  simp at h_Le
  have hi : i < m := by simp
  have hm : m > 0 := by linarith
  have hj : j < n := by simp
  have hn : n > 0 := by linarith
  rw [Add_Sub.eq.SubAdd.Ge (by linarith)] at h_Le
  rw [EqAddSub.of.Le (by nlinarith)] at h_Le
  apply Lt.of.Le_Sub_1.Gt_0 (by nlinarith)
  assumption


-- created on 2025-05-07
-- updated on 2025-05-09
