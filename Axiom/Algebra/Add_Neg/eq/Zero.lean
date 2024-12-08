import Axiom.Basic


namespace Algebra.Add_Neg.eq

@[simp]
theorem Zero
  [AddGroup α]
  {a : α} :
-- imply
  a + -a = 0 := by
-- proof
  apply add_neg_cancel


end Algebra.Add_Neg.eq

-- created on 2024-11-25
