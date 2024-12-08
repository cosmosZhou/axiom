import Axiom.Algebra.Any.equ.NotAll_Not


namespace Algebra.Any_Not.equ

theorem NotAll
  {p : α → Prop} :
-- imply
  (∃ x : α, ¬p x) ↔ ¬∀ x : α, p x := by
-- proof
  rw [Any.equ.NotAll_Not]
  simp

end Algebra.Any_Not.equ

-- created on 2024-07-01
