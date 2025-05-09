import sympy.core.relational
import Axiom.Algebra.Eq_AddMulDiv___Mod
import Axiom.Algebra.Eq_Add.of.EqSub
import Axiom.Algebra.MulSub.eq.SubMulS
import Axiom.Algebra.Sub.eq.Add_Neg
import Axiom.Algebra.AddAdd.eq.Add_Add
import Axiom.Algebra.LeAddS.of.Le
import Axiom.Algebra.LeAdd_1.of.Lt
import Axiom.Algebra.Mod.lt.Neg.of.Lt_0
open Algebra


@[main]
private lemma main
-- given
  (h : d < 0)
  (n : ℤ) :
-- imply
  ((n - 1) / d - 1) * d ≥ n := by
-- proof
  have h₀ := Eq_AddMulDiv___Mod (n := n - 1) (d := d)
  denote h_q : q = (n - 1) / d
  denote h_r : r = (n - 1) % d
  rw [← h_q]
  rw [← h_q, ← h_r] at h₀
  have := Eq_Add.of.EqSub h₀
  rw [this]
  rw [MulSub.eq.SubMulS]
  norm_num
  rw [Sub.eq.Add_Neg]
  rw [AddAdd.eq.Add_Add]
  apply LeAddS.of.Le.left (a := q * d)
  apply LeAdd_1.of.Lt
  have := Mod.lt.Neg.of.Lt_0 h (n - 1)
  rw [← h_r] at this
  assumption


-- created on 2025-03-29
-- updated on 2025-04-30
