import Axiom.Algebra.Any.equ.NotAll_Not


namespace Algebra.NotAll_Not.equ

@[simp]
theorem Any
  {p : α → Prop} :
-- imply
  (¬∀ x : α, ¬p x) ↔ ∃ x : α, p x :=
-- proof
  Any.equ.NotAll_Not.symm


end Algebra.NotAll_Not.equ

-- created on 2024-07-01
