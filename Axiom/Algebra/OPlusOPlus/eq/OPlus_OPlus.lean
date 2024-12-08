import Axiom.sympy.concrete.prefix_sum.all_prefix_sums

namespace Algebra.OPlusOPlus.eq

theorem OPlus_OPlus
  [OPlus α]
  {a b c : α} :
-- imply
  ((a ⊕ b) ⊕ c) = a ⊕ (b ⊕ c) :=
  OPlus.associative a b c



end Algebra.OPlusOPlus.eq

-- created on 2024-12-08
