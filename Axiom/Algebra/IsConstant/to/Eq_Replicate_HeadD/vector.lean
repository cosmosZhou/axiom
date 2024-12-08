import Axiom.sympy.core.containers.vector
import Axiom.Algebra.IsConstant.to.Eq_Replicate_HeadD
import Axiom.Algebra.EqValS.to.Eq

open Mathlib
namespace Algebra.IsConstant.to.Eq_Replicate_HeadD

theorem vector
  {s : Vector α n}
-- given
  (h: s is constant)
  (default : α) :
-- imply
  s = Vector.replicate n (s.headD default) := by
-- proof
  -- simp [IsConstant.is_constant] at h
  have h := IsConstant.to.Eq_Replicate_HeadD h
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
  have h_eq_vec: vec = vec' := EqValS.to.Eq h_eq_vec

  have h_eq_s : s = vec' := by rfl

  rw [h_eq_vector, h_eq_vec, h_eq_s]


end Algebra.IsConstant.to.Eq_Replicate_HeadD

-- created on 2024-07-01
