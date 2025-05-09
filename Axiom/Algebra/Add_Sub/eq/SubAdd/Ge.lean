import Axiom.Algebra.SubAdd.eq.Add_Sub.of.Le
open Algebra


@[main]
private lemma main
  {a b c : ℕ}
-- given
  (h : b ≥ c) :
-- imply
  a + (b - c) = a + b - c :=
-- proof
  (SubAdd.eq.Add_Sub.of.Le h).symm


-- created on 2025-05-07
