import Axiom.Basic


namespace Algebra.Or.to.Or

theorem symm
-- given
  (h : p ∨ q) :
-- imply
  q ∨ p :=
-- proof
  h.elim (fun p ↦ Or.inr p) (fun q ↦ Or.inl q)


end Algebra.Or.to.Or

-- created on 2024-07-01
