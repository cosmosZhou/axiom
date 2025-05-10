import Lemma.Basic


@[main]
private lemma main
  [CancelMonoidWithZero α]
  {x y d : α}
-- given
  (h₀ : x * d = y * d)
  (h₁ : d ≠ 0) :
-- imply
  x = y :=
-- proof
  (mul_left_inj' h₁).mp  h₀


-- created on 2025-04-02
