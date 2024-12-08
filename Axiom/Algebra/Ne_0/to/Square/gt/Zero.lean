import Axiom.Algebra.Square.ge.Zero
import Axiom.Algebra.Ne_0.to.Square.ne.Zero
import Axiom.Algebra.Ne.Ge.to.Gt

namespace Algebra.Ne_0.to.Square.gt

theorem Zero
  [LinearOrderedRing α]
  {a : α}
-- given
  (h : a ≠ 0) :
-- imply
  a² > 0 :=
-- proof
  Ne.Ge.to.Gt
    (Ne_0.to.Square.ne.Zero h)
    (Square.ge.Zero (a := a))



end Algebra.Ne_0.to.Square.gt

-- created on 2024-11-29
