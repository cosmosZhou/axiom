import Lemma.Basic


@[main]
private lemma main
  {x : ℝ} :
-- imply
  √x = x ^ (1 / 2 : ℝ) :=
-- proof
  -- Use the property of exponents to simplify the expression
  Real.sqrt_eq_rpow x


-- created on 2025-04-06
