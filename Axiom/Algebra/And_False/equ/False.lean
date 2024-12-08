import Axiom.Basic


namespace Algebra.And_False.equ

theorem False :
-- imply
  p ∧ False ↔ False := by
-- proof
  apply Iff.intro
  focus
    intro h
    exact h.right

  focus
    intro hf
    exact hf.elim


end Algebra.And_False.equ

-- created on 2024-07-01
