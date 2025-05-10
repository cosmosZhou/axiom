import Lemma.Basic


@[main]
private lemma nat
  {d : ℕ}
-- given
  (h : d > 0)
  (n : ℕ) :
-- imply
  n % d < d := by
-- proof
  exact Nat.mod_lt n h


@[main]
private lemma main
  {d : ℤ}
-- given
  (h : d > 0)
  (n : ℤ) :
-- imply
  n % d < d := by
-- proof
  exact Int.emod_lt_of_pos n h


-- created on 2025-03-20
-- updated on 2025-03-29
