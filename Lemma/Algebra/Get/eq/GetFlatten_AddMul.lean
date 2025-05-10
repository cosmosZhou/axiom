import stdlib.List.Vector
import Lemma.Algebra.ValGet.eq.ValSubStrFlatten
import Lemma.Algebra.Get.eq.Default.of.AddMul.ge.Mul
import Lemma.Algebra.Ge.of.NotLt
import Lemma.Algebra.GetSubstr.eq.Get_Add
open Algebra


@[main]
private lemma main
  [Inhabited α]
-- given
  (v : List.Vector (List.Vector α n) m)
  (i : Fin m)
  (j : Fin n) :
-- imply
  v[i, j] = v.flatten[i * n + j] := by
-- proof
  simp [GetElem.getElem]
  split_ifs with h
  ·
    have h_vi : v[(i : ℕ)].val = (v.flatten.substr ((i : ℕ) * n) n).val := ValGet.eq.ValSubStrFlatten v i
    have h_vi_val : v.val[(i : ℕ)].val = v[i].val := by
      simp
      simp only [GetElem.getElem]
      split_ifs with h
      ·
        simp [List.Vector.get]
      ·
        have hi := Ge.of.NotLt h
        have hi : i < m := by simp
        contradiction
    simp [List.Vector.get]
    simp [h_vi_val]
    simp [h_vi]
    have := GetSubstr.eq.Get_Add v.flatten (i * n) j
    simp [GetElem.getElem] at this
    simp [h] at this
    have h := Lt_Sub.of.LtAdd.nat.left h
    simp [h] at this
    simp [List.Vector.get] at this
    rw [this]
  ·
    have h := Ge.of.NotLt h
    have := Get.eq.Default.of.AddMul.ge.Mul h v
    simp [GetElem.getElem] at this
    assumption


-- created on 2025-05-07
-- updated on 2025-05-09
