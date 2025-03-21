import Axiom.Basic


@[main]
private lemma main
  {s : List α}
  {n : Nat}
-- given
  (h : n ≤ s.length) :
-- imply
  (s.take n |>.length) = n := by
-- proof
  induction s with
  | nil =>
    cases n with
    | zero =>
      simp [List.take]
    | succ n =>
      have : (Nat.succ n) ≤ 0 := h
      contradiction
  | cons =>
    cases n with
    | zero =>
      simp [List.take]
    | succ n =>
      simp [List.take]
      apply Nat.le_of_succ_le_succ
      assumption


-- created on 2024-07-01
