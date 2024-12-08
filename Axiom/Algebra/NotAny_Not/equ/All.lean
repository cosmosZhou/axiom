import Axiom.Algebra.All.equ.NotAny_Not


namespace Algebra.NotAny_Not.equ

theorem All
  {p : α → Prop} :
-- imply
  (¬∃ x : α, ¬p x) ↔ ∀ x : α, p x :=
-- proof
  All.equ.NotAny_Not.symm


end Algebra.NotAny_Not.equ

-- created on 2024-07-01
