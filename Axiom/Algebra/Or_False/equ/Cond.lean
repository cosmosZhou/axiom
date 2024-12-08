import Axiom.Basic


namespace Algebra.Or_False.equ

theorem Cond :
-- imply
  p ∨ False ↔ p := by
-- proof
  apply Iff.intro
  focus
    intro h
    match h with
    | Or.inl hp => exact hp
    | Or.inr hf => exact hf.elim

  focus
    intro hp
    exact Or.inl hp


end Algebra.Or_False.equ

-- created on 2024-07-01
