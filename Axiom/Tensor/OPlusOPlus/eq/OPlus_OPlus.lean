import sympy.concrete.prefix_sum.all_prefix_sums
import Axiom.Basic


@[main]
private lemma main
  [OPlus α]
  {a b c : α} :
-- imply
  ((a ⊕ b) ⊕ c) = a ⊕ (b ⊕ c) :=
  OPlus.associative a b c


-- created on 2024-12-08
