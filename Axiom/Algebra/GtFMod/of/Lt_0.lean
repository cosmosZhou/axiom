import Axiom.Algebra.NegSucc.eq.NegAdd_1
import Axiom.Algebra.SubNatNat.eq.Sub
import Axiom.Algebra.LtNegS.of.Gt
import Axiom.Algebra.LtNeg.of.Gt_Neg
import Axiom.Algebra.NegSub.eq.Sub
import Axiom.Algebra.LtMod.of.Gt_0
open Algebra


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d < 0) :
-- imply
  n.fmod d > d := by
-- proof
  unfold Int.fmod
  match n, d with
  | 0, x =>
    simp
    linarith
  | .ofNat m, .ofNat n =>
    contradiction
  | .ofNat (.succ m), .negSucc n =>
    simp
    rw [NegSucc.eq.NegAdd_1]
    rw [SubNatNat.eq.Sub]
    apply LtNeg.of.Gt_Neg
    rw [NegSub.eq.Sub]
    linarith
  | .negSucc m, .ofNat n =>
    contradiction
  | .negSucc m, .negSucc n =>
    simp
    rw [NegSucc.eq.NegAdd_1]
    apply LtNegS.of.Gt
    apply LtMod.of.Gt_0
    simp


-- created on 2025-03-28
-- updated on 2025-03-29
