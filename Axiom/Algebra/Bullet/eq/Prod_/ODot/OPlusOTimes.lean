import Axiom.sympy.concrete.prefix_sum.all_prefix_sums

namespace Algebra.Bullet.eq.Prod_.ODot

theorem OPlusOTimes
  [OPlus α]
  [OTimes α]
  [ODot α]
  [Bullet α]
  {cᵢ cj : α × α} :
-- imply
  cᵢ • cj = ⟨cᵢ.fst ⊙ cj.fst, (cᵢ.snd ⊗ cj.fst) ⊕ cj.snd⟩ :=
-- proof
  Bullet.property cᵢ cj


end Algebra.Bullet.eq.Prod_.ODot
open Algebra.Bullet.eq.Prod_.ODot
-- created on 2024-12-08
