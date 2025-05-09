import sympy.sets.sets
import Axiom.Tensor.Eq.of.EqArgsS
import Axiom.Tensor.Eq.is.EqArgsS
open Tensor


@[main]
private lemma main
  [Inhabited α]
  {a b : Tensor α (s₀ :: s)}
-- given
  (h : ∀ i ∈ range s₀, a[i] = b[i]) :
-- imply
  a = b := by
-- proof
  apply Eq.of.EqArgsS
  simp [Eq.is.EqArgsS] at h
  sorry


-- created on 2025-05-06
