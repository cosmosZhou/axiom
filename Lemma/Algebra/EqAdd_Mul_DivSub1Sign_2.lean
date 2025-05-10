import stdlib.Slice
import Lemma.Basic


@[main]
private lemma main
  {n i : ℕ} :
-- imply
  Slice.Add_Mul_DivSub1Sign_2 n i = i := by
-- proof
  unfold Slice.Add_Mul_DivSub1Sign_2
  cases i <;> simp


-- created on 2025-05-06
