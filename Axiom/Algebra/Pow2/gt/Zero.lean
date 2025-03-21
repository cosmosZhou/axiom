import Axiom.Basic
open Algebra


@[main]
private lemma main
  {n : ℕ} :
-- imply
  2 ^ n > 0 := by
-- proof
  cases n with
  | zero => 
    simp
  | succ n => 
    simp [Nat.pow_succ]


-- created on 2025-03-15
