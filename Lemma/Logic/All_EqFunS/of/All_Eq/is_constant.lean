import Lemma.Logic.All_EqFunS.of.All_Eq
open Logic


@[main]
private lemma main
  {s : Finset ι}
  {x : ι → α}
  {f : α → β}
-- given
  (h : ∀ i ∈ s, x i = a) :
-- imply
  ∀ i ∈ s, f (x i) = f a := by
-- proof
  let b := fun _ : ι => a
  have := All_EqFunS.of.All_Eq (b := b) (f := f) h
  simp only [b] at this
  assumption


-- created on 2025-04-26
