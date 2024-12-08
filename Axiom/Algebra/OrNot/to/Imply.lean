import Axiom.Basic


namespace Algebra.OrNot.to

theorem Imply
-- given
  (h : ¬p ∨ q) :
-- imply
  p → q := by
-- proof
  intro hp
  match h with
  | Or.inl hnp =>
    contradiction
  | Or.inr hq =>
    exact hq


end Algebra.OrNot.to

-- created on 2024-07-01
