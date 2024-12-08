import Axiom.Algebra.All_Not.equ.NotAny


namespace Algebra.NotAny.equ

@[simp]
theorem All_Not
  {p : α → Prop} :
-- imply
  (¬∃ x : α, p x) ↔ ∀ x : α, ¬p x :=
-- proof
  All_Not.equ.NotAny.symm

end Algebra.NotAny.equ

-- created on 2024-07-01
