import Axiom.Basic


@[main]
private lemma main
  {n : ℕ} :
-- imply
  ∑ i ∈ range n, i = n * (n - 1) / 2 := by
-- proof
  apply Finset.sum_range_id


-- created on 2024-12-21
