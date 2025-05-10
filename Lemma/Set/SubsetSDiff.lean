import Lemma.Basic


@[main]
private lemma main
  {A B : Set α} :
-- imply
  A \ B ⊆ A := by
-- proof
    -- Use the definition of set difference to show that every element of A \ B is in A.
  intro x hx
    -- By the definition of set difference, hx : x ∈ A \ B implies x ∈ A and x ∉ B.
  cases' hx with hxA hxB
    -- From hxA : x ∈ A, we directly conclude x ∈ A.
  exact hxA


-- created on 2025-04-08
-- updated on 2025-04-09
