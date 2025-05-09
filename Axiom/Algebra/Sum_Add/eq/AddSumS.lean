import sympy.core.power
import Axiom.Basic


@[main]
private lemma main
  [DecidableEq ι]
  [AddCommMonoid α]
  {s : Finset ι}
  {a b : ι → α} :
-- imply
  ∑ i ∈ s, (a i + b i) = ∑ i ∈ s, a i + ∑ i ∈ s, b i := by
-- proof
  apply Finset.induction_on (p := fun s => ∑ i ∈ s, (a i + b i) = ∑ i ∈ s, a i + ∑ i ∈ s, b i) s
  ·
    simp
  ·
    -- Inductive step: assume the statement holds for s, prove for s ∪ {j}
    intro j s hj ih
    simp_all [Finset.sum_insert hj]
    simp_all [add_assoc, add_comm, add_left_comm]


-- created on 2025-04-06
-- updated on 2025-04-27
