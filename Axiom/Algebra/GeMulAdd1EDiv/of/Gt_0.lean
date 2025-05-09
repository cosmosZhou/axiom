import sympy.core.relational
import Axiom.Algebra.Eq_AddMulDiv___Mod
import Axiom.Algebra.Eq_Add.of.EqSub
import Axiom.Algebra.MulAdd.eq.AddMulS
import Axiom.Algebra.AddAdd.rotate
import Axiom.Algebra.LeAddS.of.Le
import Axiom.Algebra.LeAdd_1.of.Lt
import Axiom.Algebra.LtMod.of.Gt_0
open Algebra


@[main]
private lemma main
-- given
  (h : d > 0)
  (n : ℤ) :
-- imply
  (1 + (n - 1) / d) * d ≥ n := by
-- proof
  -- notice that n / d means the Euclidian division, not rational division
  -- Use the Euclidean division theorem to express n - 1 as d * q + r
  have h₀ := Eq_AddMulDiv___Mod (n := n - 1) (d := d)
  denote h_q : q = (n - 1) / d
  denote h_r : r = (n - 1) % d
  rw [← h_q]
  rw [← h_q, ← h_r] at h₀
  have := Eq_Add.of.EqSub h₀
  rw [this]
  rw [MulAdd.eq.AddMulS]
  norm_num
  rw [AddAdd.rotate]
  apply LeAddS.of.Le (a := q * d)
  apply LeAdd_1.of.Lt
  have := LtMod.of.Gt_0 h (n - 1)
  rw [← h_r] at this
  assumption


-- created on 2025-03-29
