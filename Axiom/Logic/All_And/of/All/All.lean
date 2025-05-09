import Axiom.Basic


@[main]
private lemma main
  {f g : ι → Prop}
  {s : Finset ι}
-- given
  (h₀ : ∀ i ∈ s, f i)
  (h₁ : ∀ i ∈ s, g i) :
-- imply
  ∀ i ∈ s, f i ∧ g i := by
-- proof
  intro i hi
    -- Introduce the universal quantifier and set membership
  apply And.intro
    -- Split the goal into proving f i and g i separately
    -- Apply the first hypothesis h₀ to get f i
  exact h₀ i hi
    -- Apply the second hypothesis h₁ to get g i
  exact h₁ i hi


-- created on 2025-04-06
