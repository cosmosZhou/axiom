import Axiom.Algebra.AddMulS.eq.MulAdd
open Algebra


@[main]
private lemma main
  [DecidableEq ι]
  [Ring α]
  {x : α}
  {s : Finset ι}
  {a : ι → α} :
-- imply
  ∑ i ∈ s, a i * x = ∑ i ∈ s, a i * x := by
-- proof
  apply Finset.induction_on (p := fun s => ∑ i ∈ s, a i * x = ∑ i ∈ s, a i * x) s
  ·
    simp
  ·
    -- Inductive step: assume the statement holds for s, prove for s ∪ {j}
    intro j s hj ih
    simp_all [Finset.sum_insert hj]


-- created on 2025-04-06
