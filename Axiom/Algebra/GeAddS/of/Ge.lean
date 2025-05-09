import Axiom.Algebra.LeAddS.of.Le
open Algebra


@[main]
private lemma left
  [Add α]
  [LE α]
  [AddLeftMono α]
  [AddRightMono α]
  {b c : α}
-- given
  (h : b ≥ c)
  (a : α) :
-- imply
  a + b ≥ a + c :=
-- proof
  LeAddS.of.Le.left h a


@[main]
private lemma main
  [Add α]
  [LE α]
  [AddLeftMono α]
  [AddRightMono α]
  {b c : α}
-- given
  (h : b ≥ c)
  (a : α) :
-- imply
  b + a ≥ c + a :=
-- proof
  LeAddS.of.Le h a


-- created on 2024-07-01
-- updated on 2025-04-30
