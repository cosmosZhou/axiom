import Axiom.Algebra.Any.to.Cond
import Axiom.Algebra.Cond.to.Any


namespace Algebra.Any.equ

@[simp]
theorem Cond
  [Inhabited α]:
-- imply
  (∃ _ : α, r) ↔ r :=
-- proof
  ⟨Any.to.Cond, Cond.to.Any (a := default)⟩


end Algebra.Any.equ

-- created on 2024-07-01
