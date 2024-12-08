import Axiom.Basic

namespace Algebra.Le_Length.to

theorem EqLengthTake
  {s : List α}
  {n : Nat}
-- given
  (h : n ≤ s.length) :
-- imply
  (s.take n |>.length) = n := by
-- proof
  induction s generalizing n
  case nil =>
    cases n with
    | zero =>
      simp [List.take]
    | succ n =>
      have : (Nat.succ n) ≤ 0 := h
      contradiction

  case cons =>
    cases n with
    | zero =>
      simp [List.take]
    | succ n =>
      simp [List.take]
      apply Nat.le_of_succ_le_succ
      exact h
      -- the same as the following line:
      -- assumption


end Algebra.Le_Length.to

-- created on 2024-07-01
