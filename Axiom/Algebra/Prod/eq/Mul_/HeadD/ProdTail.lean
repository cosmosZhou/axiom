import Axiom.Basic

namespace Algebra.Prod.eq.Mul_.HeadD

theorem ProdTail
  [Monoid M]
  {l : List M} :
-- imply
  l.prod = l.headD 1 * l.tail.prod := by
-- proof
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]


end Algebra.Prod.eq.Mul_.HeadD

-- created on 2024-07-01
