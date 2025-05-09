import Axiom.Algebra.LtAddS.of.Lt
open Algebra


@[main]
private lemma left
  [Add α]
  [LT α]
  [AddLeftStrictMono α]
  [AddRightStrictMono α]
  {b c : α}
-- given
  (h : b > c)
  (a : α) :
-- imply
  a + b > a + c :=
-- proof
  LtAddS.of.Lt.left h a


@[main]
private lemma main
  [Add α]
  [LT α]
  [AddLeftStrictMono α]
  [AddRightStrictMono α]
  {b c : α}
-- given
  (h : b > c)
  (a : α) :
-- imply
  b + a > c + a :=
-- proof
  LtAddS.of.Lt h a


-- created on 2024-07-01
-- updated on 2025-04-30
