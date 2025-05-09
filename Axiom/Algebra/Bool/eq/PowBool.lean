import sympy.core.power
import Axiom.Basic


@[main]
private lemma main
  [Decidable p] :
-- imply
  Bool.toNat p = (Bool.toNat p) ^ (Nat.succ n) := by
-- proof
  match n with
  | .zero =>
    simp [Nat.pow_succ]     -- Simplify using the definition of Nat.pow_succ
  | .succ n =>
    by_cases h : p <;>
      simp_all [Nat.pow_succ, pow_succ]


-- created on 2025-04-20
