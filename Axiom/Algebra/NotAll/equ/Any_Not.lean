import Axiom.Algebra.Any_Not.equ.NotAll


namespace Algebra.NotAll.equ

@[simp]
theorem Any_Not
  {p : α → Prop} :
-- imply
  (¬∀ x : α, p x) ↔ ∃ x : α, ¬p x :=
-- proof
  Any_Not.equ.NotAll.symm


end Algebra.NotAll.equ

-- created on 2024-07-01
