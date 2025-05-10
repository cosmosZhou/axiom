import Lemma.Algebra.Ge_Zero
import Lemma.Algebra.Gt_Sub_1.of.Ge
open Algebra


@[main]
private lemma main
  {n : ℕ} :
-- imply
  (n : ℤ) > -1 := by
-- proof
  have := Ge_Zero (n := n)
  have := Gt_Sub_1.of.Ge this
  norm_num at this
  assumption


-- created on 2025-03-28
-- updated on 2025-03-29
