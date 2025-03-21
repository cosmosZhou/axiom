import Axiom.Basic


@[main]
private lemma main
  [LinearOrderedField α]
  [FloorRing α]
  {x : α} :
-- imply
  ⌈x⌉ = -⌊-x⌋ := by
-- proof
  -- Simplify the expression using the properties of negation and the floor function.
  simp [Int.floor_neg]


-- created on 2025-03-15
