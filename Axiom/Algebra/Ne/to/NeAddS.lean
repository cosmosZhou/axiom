import Axiom.Algebra.Eq.to.EqSubS
import Axiom.Algebra.SubAdd.cancel

namespace Algebra.Ne.to

theorem NeAddS
  [AddGroup α]
  {x y : α}
-- given
  (h : x ≠ y)
  (d : α)
  (left : Bool := false) :
-- imply
  match left with
  | true => d + x ≠ d + y
  | false => x + d ≠ y + d := by
-- proof
  cases left
  case true =>
    intro h'
    have h' := Eq.to.EqSubS h' d
    simp at h'
    exact h h'
  case false =>
    intro h'
    have h' := Eq.to.EqSubS h' d
    simp only [SubAdd.cancel] at h'
    exact h h'


end Algebra.Ne.to

-- created on 2024-11-27
