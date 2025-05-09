import sympy.sets.sets
import Axiom.Basic


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h₀ : x ∈ Ioc a b) :
-- imply
  x > a :=
-- proof
  h₀.left


-- created on 2025-03-01
