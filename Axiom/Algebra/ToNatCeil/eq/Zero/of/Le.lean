import Axiom.Algebra.LeCoeS.of.Le
import Axiom.Algebra.Sub.le.Zero.of.Le
import Axiom.Algebra.Div.le.Zero.of.Le_0.Ge_0
import Axiom.Algebra.LeCeil.of.Le
import Axiom.Algebra.ToNat.eq.Zero.of.Le_0
open Algebra


@[main]
private lemma main
  {a b d : ℕ}
-- given
  (h : a ≤ b) :
-- imply
  ⌈(a - b : ℚ) / d⌉.toNat = 0 := by
-- proof
  have h := LeCoeS.of.Le.nat (R := ℚ) h
  have h := Sub.le.Zero.of.Le h
  have h_Ge_0 : (d : ℚ) ≥ 0 := by simp
  have h_Le := Div.le.Zero.of.Le_0.Ge_0 h h_Ge_0
  have h_Le := LeCeil.of.Le h_Le
  apply ToNat.eq.Zero.of.Le_0 h_Le


-- created on 2025-05-05
