import Axiom.Algebra.Le.of.Lt
import Axiom.Algebra.Ne.of.Lt
open Algebra


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : a > b) :
-- imply
  a ≥ b ∧ a ≠ b := by
-- proof
  -- We need to prove two parts: a ≥ b and a ≠ b.
  constructor
  ·
    -- First part: a ≥ b.
    -- Since a > b implies a ≤ b is false and b ≤ a is true, we use the fact that b ≤ a implies a ≥ b.
    exact Le.of.Lt h
  ·
    -- Second part: a ≠ b.
    -- Assume a = b for contradiction. By antisymmetry, a ≤ b and b ≤ a would hold, contradicting a ≤ b being false.
    apply Ne.symm (Ne.of.Lt h)


-- created on 2025-04-18
