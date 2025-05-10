import Lemma.Basic


@[main]
private lemma main
  {s: List α}
  {i : Nat}
-- given
  (h: i ≤ s.length) :
-- imply
  (s.drop i |>.length) = s.length - i := by
-- proof
  induction s <;> simp [List.drop]


-- created on 2024-07-01
