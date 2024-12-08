import Axiom.Algebra.Any.equ.NotAll_Not


namespace Algebra.All.equ

theorem NotAny_Not
  {p : α → Prop} :
-- imply
  (∀ x : α, p x) ↔ ¬∃ x : α, ¬p x := by
-- proof
  rw [Any.equ.NotAll_Not]
  simp

end Algebra.All.equ

-- created on 2024-07-01
