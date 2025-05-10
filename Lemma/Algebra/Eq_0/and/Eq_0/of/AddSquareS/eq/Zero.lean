import Lemma.Algebra.Square.ge.Zero
import Lemma.Algebra.Eq_0.and.Eq_0.of.Ge_0.Ge_0.Add.eq.Zero
import Lemma.Algebra.Eq_0.of.Square.eq.Zero
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {x y : α}
-- given
  (h : x² + y² = 0) :
-- imply
  x = 0 ∧ y = 0 := by
-- proof
  have h_x := Square.ge.Zero (a := x)
  have h_y := Square.ge.Zero (a := y)
  have ⟨h_x, h_y⟩ := Eq_0.and.Eq_0.of.Ge_0.Ge_0.Add.eq.Zero h_x h_y h
  have := Eq_0.of.Square.eq.Zero h_x
  have := Eq_0.of.Square.eq.Zero h_y
  constructor <;> assumption


-- created on 2025-01-17
-- updated on 2025-01-26
