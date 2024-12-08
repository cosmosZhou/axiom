import Axiom.Algebra.And_Or.to.OrAndS
import Axiom.Algebra.AndAndNot.equ.False
import Axiom.Algebra.AndAnd_Not.equ.False

namespace Algebra.AndNotS.to

theorem NotOr
-- given
  (h : ¬p ∧ ¬q) :
-- imply
  ¬(p ∨ q) := by
-- proof
  by_contra h_Or
  have h := And.intro h h_Or
  have h := And_Or.to.OrAndS h
  simp at h


end Algebra.AndNotS.to

-- created on 2024-07-01
