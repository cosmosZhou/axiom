import stdlib.List.Vector
import Axiom.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h : s is constant)
  (default : α) :
-- imply
  ∀ x ∈ s, x = s.headD default := by
-- proof
  match s with
  | .nil =>
    simp [IsConstant.is_constant]
  | .cons x xs =>
    simp [IsConstant.is_constant] at *
    intro x x_in_s
    exact h x x_in_s


-- created on 2024-07-01
