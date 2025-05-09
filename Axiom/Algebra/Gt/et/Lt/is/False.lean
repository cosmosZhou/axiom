import Axiom.Algebra.Lt.of.Lt.Lt
import Axiom.Algebra.NotLt
open Algebra


@[main]
private lemma main
  [LinearOrder α]
  {a b : α} :
-- imply
  a > b ∧ a < b ↔ False := by
-- proof
  constructor
  ·
    intro h
    let ⟨h₀, h₁⟩ := h
    have := Lt.of.Lt.Lt h₀ h₁
    apply NotLt this
  ·
    intro h
    contradiction


-- created on 2025-03-26
-- updated on 2025-03-27
