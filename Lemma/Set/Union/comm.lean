import Lemma.Basic


@[main]
private lemma finset
  [DecidableEq ι]
  {a b : Finset ι} :
-- imply
  a ∪ b = b ∪ a := by
-- proof
  rw [Finset.union_comm]


@[main]
private lemma main
  {a b : Set α} :
-- imply
  a ∪ b = b ∪ a := by
-- proof
  rw [Set.union_comm]


-- created on 2024-12-21
