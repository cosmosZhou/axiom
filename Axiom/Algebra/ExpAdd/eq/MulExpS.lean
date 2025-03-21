import Axiom.Basic


@[main]
private lemma main
  {a b : ℝ} :
-- imply
  exp (a + b) = exp a * exp b := by
-- proof
  apply Real.exp_add


-- created on 2025-01-05
