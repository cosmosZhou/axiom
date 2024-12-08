import Axiom.Algebra.Iff.to.IffNotS
namespace Algebra.Iff_Not.to

theorem Iff_Not
  {p q : Prop}
-- given
  (h : p ↔ ¬q) :
-- imply
  q ↔ ¬p := by
-- proof
  have h := Iff.to.IffNotS h
  simp at h
  exact h.symm


end Algebra.Iff_Not.to

-- created on 2024-07-01
