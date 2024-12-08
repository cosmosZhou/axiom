import Axiom.Algebra.Any_Or.to.OrAnyS
import Axiom.Algebra.OrAnyS.to.Any_Or


namespace Algebra.Any_Or.equ

theorem OrAnyS
  {p q : α → Prop} :
-- imply
  (∃ x : α, p x ∨ q x) ↔  (∃ x : α, p x) ∨ (∃ x : α, q x) :=
-- proof
  ⟨Any_Or.to.OrAnyS, OrAnyS.to.Any_Or⟩

end Algebra.Any_Or.equ

-- created on 2024-07-01
