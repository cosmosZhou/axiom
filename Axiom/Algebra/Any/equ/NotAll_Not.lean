import Axiom.Algebra.Any.to.NotAll_Not
import Axiom.Algebra.NotAll_Not.to.Any


namespace Algebra.Any.equ

theorem NotAll_Not
  {p : α → Prop} :
-- imply
  (∃ x : α, p x) ↔ ¬∀ x : α, ¬p x :=
-- proof
  ⟨Any.to.NotAll_Not, NotAll_Not.to.Any⟩


end Algebra.Any.equ

-- created on 2024-07-01
