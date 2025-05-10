import Lemma.Basic


@[main]
private lemma main
  [CancelMonoidWithZero α]
  {x y d : α}
-- given
  (h₀ : d ≠ 0)
  (h₁ : d * x = d * y) :
-- imply
  x = y :=
-- proof
  (mul_right_inj' h₀).mp h₁


-- created on 2025-04-02
