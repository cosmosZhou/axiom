import sympy.functions.elementary.integers
import Axiom.Algebra.NegSucc.eq.NegAdd_1
import Axiom.Algebra.EqNegNeg
import Axiom.Algebra.EDiv_Neg.eq.NegEDiv
open Algebra


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h₀ : n < 0)
  (h₁ : d < 0) :
-- imply
  n // d = -(-n / d) := by
-- proof
  unfold Int.fdiv
  match n, d with
  | 0, x =>
    contradiction
  | .ofNat m, .ofNat n =>
    contradiction
  | .ofNat (.succ m), .negSucc n =>
    contradiction
  | .negSucc a, 0 =>
    contradiction
  | .negSucc m, .ofNat (.succ n) =>
    contradiction
  | .negSucc m, .negSucc n =>
    simp [Int.negSucc]
    rw [NegSucc.eq.NegAdd_1]
    rw [NegSucc.eq.NegAdd_1]
    rw [EqNegNeg]
    rw [EDiv_Neg.eq.NegEDiv]
    rw [EqNegNeg]


-- created on 2025-03-28
-- updated on 2025-03-29
