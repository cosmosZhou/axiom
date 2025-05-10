import Lemma.Basic


@[main]
private lemma main
  [DecidableEq ι]
  [CommMonoid α]
  {s : Finset ι}
  {a b : ι → α} :
-- imply
  ∏ i ∈ s, a i * b i = (∏ i ∈ s, a i) * ∏ i ∈ s, b i := by
-- proof
  apply Finset.induction_on (p := fun s => ∏ i ∈ s, a i * b i = (∏ i ∈ s, a i) * ∏ i ∈ s, b i) s
  ·
    -- Base case: when s is empty, both sides are 1 (empty product)
    simp
  ·
    -- Inductive step: assume the statement holds for s, prove for s ∪ {j}
    intro j s hj ih
    simp_all [Finset.prod_insert hj]
    simp_all [mul_assoc, mul_comm, mul_left_comm]


-- created on 2025-04-27
