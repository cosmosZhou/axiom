import stdlib.List.Vector
import Axiom.Algebra.GetTake.eq.Get
import Axiom.Algebra.Ge.of.NotLt
import Axiom.Algebra.GetDrop.eq.Get_Add
import Axiom.Algebra.Ge_Sub.of.GeAdd
import Axiom.Algebra.Lt_Sub.of.LtAdd
open Algebra


@[main]
private lemma main
  [Inhabited α]
-- given
  (v : List.Vector α N)
  (m : ℕ)
  (j : Fin n) :
-- imply
  (v.substr m n)[j] = v[m + j] := by
-- proof
  simp [List.Vector.substr]
  simp only [(show (List.Vector.take n (List.Vector.drop m v))[(j : ℕ)] = (List.Vector.drop m v)[j] by apply GetTake.eq.Get (List.Vector.drop m v) j)]
  simp [GetElem.getElem]
  split_ifs with h₀ h₁ h₂
  ·
    have := GetDrop.eq.Get_Add v m j
    simp [GetElem.getElem] at this
    simp [h₀, h₁] at this
    assumption
  ·
    have h₁ := Ge.of.NotLt h₁
    have h₁ := Ge_Sub.of.GeAdd.nat.left h₁
    linarith
  ·
    have h₀ := Ge.of.NotLt h₀
    have h₂ := Lt_Sub.of.LtAdd.nat.left h₂
    linarith
  ·
    rfl


-- created on 2025-05-09
