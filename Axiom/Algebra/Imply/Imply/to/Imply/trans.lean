import Axiom.Basic
namespace Algebra.Imply.Imply.to.Imply

theorem trans
  {p q r : Prop}
-- given
  (h₀ : p → q)
  (h₁ : q → r) :
-- imply
  p → r :=
-- proof
  fun h : p =>
    h₁ (h₀ h)


end Algebra.Imply.Imply.to.Imply

-- created on 2024-07-01
