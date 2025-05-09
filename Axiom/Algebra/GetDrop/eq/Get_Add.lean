import stdlib.List.Vector
import Axiom.Algebra.Ge.of.NotLt
import Axiom.Algebra.Ge_Sub.of.GeAdd
import Axiom.Algebra.Lt_Sub.of.LtAdd
open Algebra


@[main]
private lemma main
  [Inhabited α]
-- given
  (v : List.Vector α m)
  (n j : ℕ) :
-- imply
  (v.drop n)[j] = v[n + j] := by
-- proof
  simp [GetElem.getElem]
  split_ifs with h₀ h₁ h₂
  ·
    simp [List.Vector.get]
    simp [List.Vector.drop]
    cases v
    simp
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
