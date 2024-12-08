import Axiom.sympy.concrete.prefix_sum.all_prefix_sums
import Axiom.Algebra.Bullet.eq.Prod_.ODot.OPlusOTimes
import Axiom.Algebra.ODotODot.eq.ODot_ODot
import Axiom.Algebra.OTimes_OPlus.eq.OPlusOTimesS
import Axiom.Algebra.OPlusOPlus.eq.OPlus_OPlus
import Axiom.Algebra.OTimesOTimes.eq.OTimes_ODot
namespace Algebra.BulletBullet.eq

-- http://shelf2.library.cmu.edu/Tech/23445461.pdf#page=15
theorem Bullet_Bullet
  [OPlus α]
  [OTimes α]
  [ODot α]
  [Bullet α]
  {cᵢ cj cₖ : α × α} :
-- imply
  (cᵢ • cj) • cₖ = cᵢ • (cj • cₖ) := by
-- proof
  rw [Bullet.eq.Prod_.ODot.OPlusOTimes (cj := cj)]
  rw [Bullet.eq.Prod_.ODot.OPlusOTimes (cj := cₖ)]
  simp
  rw [ODotODot.eq.ODot_ODot]
  rw [OTimes_OPlus.eq.OPlusOTimesS]
  rw [OPlusOPlus.eq.OPlus_OPlus]
  rw [OTimesOTimes.eq.OTimes_ODot]
  rw [←Bullet.eq.Prod_.ODot.OPlusOTimes (cj := ⟨cj.fst ⊙ cₖ.fst, (cj.snd ⊗ cₖ.fst) ⊕ cₖ.snd⟩)]
  rw [←Bullet.eq.Prod_.ODot.OPlusOTimes (cj := cₖ)]


end Algebra.BulletBullet.eq
-- created on 2024-12-08
