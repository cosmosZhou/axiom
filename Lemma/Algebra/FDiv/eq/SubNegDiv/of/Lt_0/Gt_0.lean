import sympy.functions.elementary.integers
import Lemma.Algebra.NegSucc.eq.NegAdd_1
import Lemma.Algebra.EqNegNeg
import Lemma.Algebra.EqSubAdd
import Lemma.Algebra.SubNeg.eq.NegAdd
open Algebra


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h₀ : n < 0)
  (h₁ : d > 0) :
-- imply
  n // d = -((-n - 1) / d) - 1 := by
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
    simp [Int.negSucc]
    rw [NegSucc.eq.NegAdd_1]
    rw [NegSucc.eq.NegAdd_1]
    rw [EqNegNeg]
    rw [EqSubAdd]
    rw [SubNeg.eq.NegAdd]
    norm_cast
  | .negSucc m, .negSucc n =>
    contradiction


-- created on 2025-03-28
-- updated on 2025-03-29
