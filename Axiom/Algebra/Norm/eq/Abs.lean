import Axiom.Basic


@[main]
private lemma main
  {a : ℂ} :
-- imply
  ‖a‖ = abs a :=
-- proof
  Complex.norm_eq_abs a


-- created on 2025-01-15
