import Axiom.Algebra.NegSucc.eq.NegAdd_1
import Axiom.Algebra.Gt_Neg1
open Algebra


@[main]
private lemma main
  {n : ℕ} :
-- imply
  Int.negSucc n < 0 := by
-- proof
  -- Simplify the goal using the definition of `Int.negSucc`
  simp [NegSucc.eq.NegAdd_1]
  -- Use linear arithmetic to conclude the proof, leveraging that `n + 1 > 0` for any natural number `n`
  apply Gt_Neg1


-- created on 2025-03-28
-- updated on 2025-03-29
