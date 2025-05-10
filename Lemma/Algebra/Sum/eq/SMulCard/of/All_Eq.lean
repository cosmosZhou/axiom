import Lemma.Algebra.EqSumS.of.All_Eq
open Algebra


@[main]
private lemma main
  [AddCommMonoid α]
  {s : Finset ι}
  {x : ι → α}
  {a : α}
-- given
  (h : ∀ i ∈ s, x i = a) :
-- imply
  ∑ i ∈ s, x i = s.card • a := by
-- proof
  let y := fun _ : ι => a
  have := EqSumS.of.All_Eq (y := y) h
  simp [y] at this
  assumption


-- created on 2025-04-26
