import Axiom.Algebra.Any_And.to.AndAny
import Axiom.Algebra.AndAny.to.Any_And


namespace Algebra.Any_And.equ

theorem AndAny
  {r :Prop}
  {p : α → Prop} :
-- imply
  (∃ x : α, p x ∧ r) ↔ (∃ x : α, p x) ∧ r :=
-- proof
  ⟨Any_And.to.AndAny, AndAny.to.Any_And⟩


end Algebra.Any_And.equ

-- created on 2024-07-01
