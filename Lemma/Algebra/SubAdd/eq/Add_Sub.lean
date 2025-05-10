import Lemma.Algebra.Add_Sub.eq.SubAdd
open Algebra


@[main]
private lemma main
  [SubNegMonoid α]
  {a b c : α} :
-- imply
  a + b - c = a + (b - c) := by
-- proof
  rw [Add_Sub.eq.SubAdd]


-- created on 2024-07-01
