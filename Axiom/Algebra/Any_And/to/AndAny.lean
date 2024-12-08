import Axiom.Algebra.Any_And.to.Any
import Axiom.Algebra.Any.to.Cond

namespace Algebra.Any_And.to

theorem AndAny
  {r :Prop}
  {p : α → Prop}
-- given
  (h : ∃ x : α, p x ∧ r) :
-- imply
  (∃ x : α, p x) ∧ r :=
-- proof
  ⟨
    Any_And.to.Any h,
    Any.to.Cond (
      Any_And.to.Any h false
    )
  ⟩


end Algebra.Any_And.to

-- created on 2024-07-01
