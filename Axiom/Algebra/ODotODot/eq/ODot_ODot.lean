import Axiom.sympy.concrete.prefix_sum.all_prefix_sums

namespace Algebra.ODotODot.eq

theorem ODot_ODot
  [OPlus α]
  [OTimes α]
  [ODot α]
  {a b c : α} :
-- imply
  (a ⊙ b) ⊙ c = a ⊙ (b ⊙ c) :=
  ODot.associative a b c


end Algebra.ODotODot.eq
open Algebra.ODotODot.eq
-- created on 2024-12-08
