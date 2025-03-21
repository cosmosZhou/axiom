import Axiom.Algebra.Eq_Replicate_HeadD.of.IsConstant
import Axiom.Algebra.Eq.of.EqValS
open Mathlib Algebra


@[main]
private lemma main
  {s : Vector α n}
-- given
  (h: s is constant)
  (default : α) :
-- imply
  s = Vector.replicate n (s.headD default) := by
-- proof
  have h := Eq_Replicate_HeadD.of.IsConstant h
  have h : s.val = List.replicate s.val.length (s.val.headD default) := h default
  have h_eq_length : s.val.length = s.length := by simp [Vector.length]
  have h_eq_headD : s.val.headD default = s.headD default := by rfl
  rw [h_eq_length, h_eq_headD] at h
  let vec : Vector α n := ⟨
    List.replicate s.length (s.headD default),
    by simp [h_eq_length]
  ⟩
  have h_eq_vector : Vector.replicate s.length (s.headD default) = vec := by rfl
  let vec' : Vector α n := ⟨
    s.val,
    h_eq_length
  ⟩
  have h_eq_vec : vec.val = vec'.val := by simp [h]
  have h_eq_vec: vec = vec' := Eq.of.EqValS h_eq_vec
  have h_eq_s : s = vec' := by rfl
  rw [h_eq_vector, h_eq_vec, h_eq_s]


-- created on 2024-07-01
