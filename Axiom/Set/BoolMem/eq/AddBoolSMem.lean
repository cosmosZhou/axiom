import Axiom.Set.Mem.is.Mem_Inter.ou.Mem_SDiff
import Axiom.Logic.EqBoolS.of.Iff
import Axiom.Logic.BoolOr.eq.SubAddBoolS
import Axiom.Set.AndMemS.is.Mem_Inter
import Axiom.Set.InterInter.eq.Inter_Inter
open Set Logic


@[main]
private lemma finset
  [DecidableEq α]
  {A B : Finset α}
  {x : α} :
-- imply
  Bool.toNat (x ∈ A) = Bool.toNat (x ∈ A ∩ B) + Bool.toNat (x ∈ A \ B) := by
-- proof
  have := Mem.is.Mem_Inter.ou.Mem_SDiff.finset (x := x) (A := A) (B := B)
  have := EqBoolS.of.Iff this
  rw [BoolOr.eq.SubAddBoolS] at this
  rw [this]
  suffices h : Bool.toNat (x ∈ A ∩ B ∧ x ∈ A \ B) = 0 by
    rw [h]
    simp
  simp only [AndMemS.is.Mem_Inter.finset]
  simp


@[main]
private lemma main
  [DecidableRel (· ∈ · : α → Set α → Prop)]
  {A B : Set α}
  {x : α} :
-- imply
  Bool.toNat (x ∈ A) = Bool.toNat (x ∈ A ∩ B) + Bool.toNat (x ∈ A \ B) := by
-- proof
  have := Mem.is.Mem_Inter.ou.Mem_SDiff (x := x) (A := A) (B := B)
  have := EqBoolS.of.Iff this
  rw [BoolOr.eq.SubAddBoolS] at this
  rw [this]
  suffices h : Bool.toNat (x ∈ A ∩ B ∧ x ∈ A \ B) = 0 by
    rw [h]
    simp
  simp only [AndMemS.is.Mem_Inter]
  simp only [InterInter.eq.Inter_Inter]
  simp


-- created on 2025-05-01
