import Axiom.Basic


@[main]
private lemma main
  {a b : Set α} :
-- imply
  a ∩ b = b ∩ a := by
-- proof
  rw [Set.inter_comm]


-- created on 2024-12-21
