import Axiom.Algebra.Sub_Sub.eq.AddSub
import Axiom.Algebra.Sub.eq.Zero
import Axiom.Algebra.EqAdd0
open Algebra


@[main]
private lemma main
  [AddCommGroup α]
  {a b : α} :
-- imply
  a - (a - b) = b := by
-- proof
  rw [Sub_Sub.eq.AddSub]
  rw [Sub.eq.Zero]
  rw [EqAdd0]


-- created on 2025-04-06
