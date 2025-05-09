import Axiom.Trigonometry.ExpMulI.eq.AddCos_MulISin.Euler
import Axiom.Algebra.Expr.eq.AddRe_MulIIm
import Axiom.Logic.Eq.of.Eq.Eq.trans
import Axiom.Algebra.Mul_Add.eq.AddMulS
import Axiom.Trigonometry.Re.eq.MulAbs_CosArg
import Axiom.Trigonometry.Im.eq.MulAbs_SinArg
import Axiom.Algebra.Eq.of.EqReS.EqImS
open Algebra Logic Trigonometry


@[main]
private lemma main
  {z : ℂ} :
-- imply
  z = ‖z‖ * (I * arg z).exp := by
-- proof
  rw [ExpMulI.eq.AddCos_MulISin.Euler]
  apply Eq.of.Eq.Eq.trans (f := fun z _ => ↑z.re + I * ↑z.im) (h_a := (Expr.eq.AddRe_MulIIm (z := z)).symm)
  rw [Mul_Add.eq.AddMulS]
  apply Eq.of.EqReS.EqImS
  simp at *
  have h_Eq : (z.arg : ℂ).cos.re = cos z.arg := by
    simp [cos]
  rw [h_Eq]
  apply Re.eq.MulAbs_CosArg (z := z)
  simp at *
  have h_Eq : (z.arg : ℂ).sin.re = sin z.arg := by
    simp [sin]
  rw [h_Eq]
  apply Im.eq.MulAbs_SinArg (z := z)


-- created on 2025-01-13
