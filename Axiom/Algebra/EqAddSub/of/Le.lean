import Axiom.Basic


@[main]
private lemma main
  {n m : ℕ}
-- given
  (h : m ≤ n) :
-- imply
  n - m + m = n :=
-- proof
  Nat.sub_add_cancel h


-- created on 2025-03-15
