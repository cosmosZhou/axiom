import Lemma.Basic


@[main]
private lemma main
  {a b : ℂ} :
-- imply
  (a + b).exp = a.exp * b.exp := by
-- proof
  apply Complex.exp_add


-- created on 2025-01-05
