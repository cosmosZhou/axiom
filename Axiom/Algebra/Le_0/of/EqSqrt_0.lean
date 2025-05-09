import Axiom.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : √x = 0) :
-- imply
  x ≤ 0 :=
-- proof
  Real.sqrt_eq_zero'.mp h


-- created on 2025-01-17
