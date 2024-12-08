import Axiom.Algebra.Square.eq.Mul
namespace Algebra.Mul.eq

theorem Square
  [Monoid α]
  {x : α} :
-- imply
  x * x = x² := by
-- proof
  rw [Square.eq.Mul]


end Algebra.Mul.eq

-- created on 2024-07-01
