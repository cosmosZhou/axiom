import Axiom.sympy.core.containers.list
import Axiom.Algebra.All_Eq_.SumMap_FunMul.DotMapS
import Axiom.Algebra.AddMulS.eq.MulAdd

namespace Algebra.SumMap_FunMul.eq

theorem MulSumMap
  -- [AddMonoid β]
  [Add β] [MulZeroClass β] [RightDistribClass β]
  {s : List α}
  {f : α → β}
  {const : β} :
-- imply
  (s.map fun x => (f x) * const).sum = (s.map f).sum * const := by
-- proof
  induction s with
  | nil =>
    -- Base case: s is the empty list
    simp [List.sum_nil]
  | cons a s ih =>
    -- Inductive case: s is a non-empty list
    simp [List.sum_cons, ih, AddMulS.eq.MulAdd]


end Algebra.SumMap_FunMul.eq

-- created on 2024-07-01
