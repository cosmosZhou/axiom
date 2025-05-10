import Lemma.Basic


@[main]
private lemma main
  {a b x : α}
-- given
  (h₀ : b = x)
  (h₁ : x = a) :
-- imply
  b = a :=
-- proof
  Eq.trans h₀ h₁


-- created on 2025-04-20
