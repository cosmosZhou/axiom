import Axiom.Basic


@[main]
private lemma main
  {a b c : Set α} :
-- imply
  a ∩ b ∩ c = a ∩ (b ∩ c) := by
-- proof
  rw [Set.inter_assoc]


-- created on 2024-12-21
