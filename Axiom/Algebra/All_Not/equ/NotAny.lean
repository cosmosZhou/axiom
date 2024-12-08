import Axiom.Algebra.All.equ.NotAny_Not


namespace Algebra.All_Not.equ

theorem NotAny
  {p : α → Prop} :
-- imply
  (∀ x : α, ¬p x) ↔ ¬∃ x : α, p x := by
-- proof
  rw [All.equ.NotAny_Not]
  simp


end Algebra.All_Not.equ

-- created on 2024-07-01
