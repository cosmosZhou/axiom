import Axiom.Basic


@[main]
private lemma main
  [InvolutiveNeg α]
  {x y : α}
-- given
  (h : -x = -y) :
-- imply
  x = y := by
-- proof
  apply neg_inj.mp
  -- Use the given hypothesis -x = -y to conclude x = y.
  exact h


-- created on 2025-03-16
