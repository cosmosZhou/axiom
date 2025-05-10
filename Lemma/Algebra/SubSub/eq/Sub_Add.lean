import Lemma.Algebra.Sub_Add.eq.SubSub
open Algebra


@[main]
private lemma nat
  {a b c : ℕ} :
-- imply
  a - b - c = a - (b + c) := by
-- proof
  rw [← Sub_Add.eq.SubSub.nat]


@[main]
private lemma main
  [SubtractionCommMonoid α]
  {a b c : α} :
-- imply
  a - b - c = a - (b + c) := by
-- proof
  rw [← Sub_Add.eq.SubSub]


-- created on 2025-03-24
-- updated on 2025-03-31
