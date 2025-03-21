import Axiom.Basic
open Mathlib


@[simp, main]
private lemma main
  [Add α] [Zero α]
  {s : Vector α 0} :
-- imply
  s.sum = 0 := by
-- proof
  match s with
  | ⟨v, property⟩ =>
    simp [Vector.sum] at property
    simp [Vector.sum, property]


-- created on 2024-07-01
