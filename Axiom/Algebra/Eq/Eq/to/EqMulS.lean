import Axiom.Basic
namespace Algebra.Eq.Eq.to


theorem EqMulS
  {α : Type _} [Mul α]
  {a b x y : α}
-- given
  (h1 : a = b)
  (h2 : x = y) :
-- imply
  a * x = b * y := by
-- proof
  rw [h1, h2]

end Algebra.Eq.Eq.to

-- created on 2024-07-01
