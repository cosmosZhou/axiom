import Axiom.Algebra.EqSubS.of.Eq
import Axiom.Algebra.EqAddS.of.Eq
import Axiom.Algebra.SubSquareS.eq.MulAdd__Sub
import Axiom.Algebra.OrEqS_0.of.Mul.eq.Zero
open Algebra


@[main]
private lemma main
  [Field α]
  {x c : α}
-- given
  (h : x² = c²) :
-- imply
  x = c ∨ x = -c := by
-- proof
  have h := EqSubS.of.Eq h c²
  simp at h
  rw [SubSquareS.eq.MulAdd__Sub] at h
  have h := OrEqS_0.of.Mul.eq.Zero h
  cases h with
  | inl h =>
    have h := EqSubS.of.Eq h c
    simp at h
    exact Or.inr h
  | inr h =>
    have h := EqAddS.of.Eq h c
    simp at h
    exact Or.inl h


-- created on 2024-07-01
-- updated on 2025-04-05
