import sympy.concrete.prefix_sum.all_prefix_sums
import Axiom.Basic


@[main]
private lemma main
  [OPlus α]
  [OTimes α]
  {a b c : α} :
-- imply
  (a ⊕ b) ⊗ c = a ⊗ c ⊕ b ⊗ c :=
-- proof
  OTimes.distributive a b c


-- created on 2024-12-08
