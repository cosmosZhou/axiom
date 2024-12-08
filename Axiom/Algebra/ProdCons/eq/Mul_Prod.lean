import Axiom.Basic

namespace Algebra.ProdCons.eq

theorem Mul_Prod
  [Monoid M]
  {l : List M} {a : M} :
-- imply
  (a :: l).prod = a * l.prod :=
-- proof
  List.prod_cons


end Algebra.ProdCons.eq

-- created on 2024-07-01
