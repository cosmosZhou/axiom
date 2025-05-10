import Lemma.Basic


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : p ∧ q ∨ p) :
-- imply
  p := by
-- proof
  cases' h with h_pq hp
  ·
    exact h_pq.left
  ·
    assumption


-- created on 2025-04-14
