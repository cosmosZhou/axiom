import Axiom.Basic
open Algebra


@[main]
private lemma main
  {n k : ℕ} :
-- imply
  n + k ≡ k [MOD n] := by
-- proof
  simp [Nat.ModEq]


-- created on 2025-03-15
