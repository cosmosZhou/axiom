import Axiom.Algebra.SumCons.eq.Add_Sum.vector
import Axiom.Algebra.Sum.eq.Zero
import Axiom.Algebra.EqHeadD
import Axiom.Algebra.EqHeadDCons
open Algebra


@[main]
private lemma main
  [AddMonoid α]
  {l : Vector α n} :
-- imply
  l.sum = (l.headD 0) + l.tail.sum := by
-- proof
  cases n with
  | zero =>
    simp [EqHeadD, Sum.eq.Zero]
  | succ n =>
    have h : l = l.head ::ᵥ l.tail := by simp
    rw [h]
    rw [
      SumCons.eq.Add_Sum.vector,
      EqHeadDCons
    ]
    simp


-- created on 2024-07-01
