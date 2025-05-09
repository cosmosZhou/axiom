import Axiom.Algebra.AddMulS.eq.Mul_Add
open Algebra


@[main]
private lemma main
  [DecidableEq ι]
  [Ring α]
  {x : α}
  {s : Finset ι}
  {a : ι → α} :
-- imply
  ∑ i ∈ s, x * a i = x * ∑ i ∈ s, a i := by
-- proof
  apply Finset.induction_on (p := fun s => ∑ i ∈ s, x * a i = x * ∑ i ∈ s, a i) s
  ·
    simp
  ·
    -- Inductive step: assume the statement holds for s, prove for s ∪ {j}
    intro j s hj ih
    simp_all [Finset.sum_insert hj]
    apply AddMulS.eq.Mul_Add


-- created on 2025-04-06
