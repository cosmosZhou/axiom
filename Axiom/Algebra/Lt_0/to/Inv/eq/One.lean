import Axiom.Algebra.Lt.to.Ne
import Axiom.Algebra.Ne_0.to.Div.eq.One


namespace Algebra.Lt_0.to.Inv.eq

theorem One
  [Preorder α]
  [GroupWithZero α]
  {x : α}
-- given
  (h : x < 0) :
-- imply
  x / x = 1 :=
-- proof
  (Ne_0.to.Div.eq.One ∘ Lt.to.Ne) h


end Algebra.Lt_0.to.Inv.eq

-- created on 2024-11-25
