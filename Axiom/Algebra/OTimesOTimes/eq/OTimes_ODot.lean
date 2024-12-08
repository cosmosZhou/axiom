import Axiom.sympy.concrete.prefix_sum.all_prefix_sums

namespace Algebra.OTimesOTimes.eq

theorem OTimes_ODot
  [OPlus α]
  [OTimes α]
  [ODot α]
  {a b c : α} :
-- imply
  ((a ⊗ b) ⊗ c) = a ⊗ (b ⊙ c) :=
  ODot.semiassociative a b c


end Algebra.OTimesOTimes.eq
open Algebra.OTimesOTimes.eq
-- created on 2024-12-08
