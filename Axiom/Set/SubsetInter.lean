import Axiom.Basic


@[main]
private lemma main
  {A B : Set α} :
-- imply
  A ∩ B ⊆ B := by
-- proof
    -- Introduce an arbitrary element x in the intersection of A and B.
  intro x hx
    -- By the definition of intersection, x must be in both A and B.
  cases' hx with hxA hxB
    -- Since x is in B by the definition of intersection, we can directly conclude x ∈ B.
  exact hxB


-- created on 2025-04-08
