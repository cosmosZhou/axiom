import Axiom.Basic
open Mathlib


@[simp, main]
private lemma main
  [Add α] [Zero α] [Mul α]
  {x y : Vector α 0} :
-- imply
  x ⬝ y = 0 := by
-- proof
  match x, y with
  | ⟨x, xProperty⟩, ⟨y, yProperty⟩ =>
    simp [Vector.dot] at xProperty yProperty
    simp [Vector.dot, xProperty, yProperty]


-- created on 2024-07-01
