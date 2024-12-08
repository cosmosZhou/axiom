import Axiom.sympy.concrete.prefix_sum.all_prefix_sums

namespace Algebra.OTimes_OPlus.eq

theorem OPlusOTimesS
  [OPlus α]
  [OTimes α]
  {a b c : α} :
-- imply
  (a ⊕ b) ⊗ c = a ⊗ c ⊕ b ⊗ c :=
-- proof
  OTimes.distributive a b c


end Algebra.OTimes_OPlus.eq
open Algebra.OTimes_OPlus.eq
-- created on 2024-12-08
