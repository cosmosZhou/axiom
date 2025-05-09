import Axiom.Algebra.LeSub.of.Le_Add
open Algebra


@[main]
private lemma nat
  {a b c : ℕ}
-- given
  (h : a + b ≥ c) :
-- imply
  a ≥ c - b :=
-- proof
  LeSub.of.Le_Add.nat h


@[main]
private lemma nat.left
  {a b c : ℕ}
-- given
  (h : a + b ≥ c) :
-- imply
  b ≥ c - a :=
-- proof
  LeSub.of.Le_Add.nat.left h


@[main]
private lemma left
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : a + b ≥ c) :
-- imply
  b ≥ c - a := 
-- proof
  LeSub.of.Le_Add.left h


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : a + b ≥ c) :
-- imply
  a ≥ c - b :=
-- proof
  LeSub.of.Le_Add h


-- created on 2024-11-27
-- updated on 2025-05-09
