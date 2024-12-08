import Axiom.Algebra.Gt.to.Ne
import Axiom.Algebra.Ne_0.to.Div.eq.One

namespace Algebra.Gt_0.to.Div.eq


theorem One
  [Preorder α]
  [GroupWithZero α]
  {x : α}
-- given
  (h : x > 0) :
-- imply
  x / x = 1 :=
-- proof
  (Ne_0.to.Div.eq.One ∘ Gt.to.Ne) h


end Algebra.Gt_0.to.Div.eq

-- created on 2024-11-25
