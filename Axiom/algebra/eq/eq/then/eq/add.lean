namespace algebra.eq.eq.then.eq

theorem add
  {α : Type _} [Add α]
  {a b x y : α}
-- given
  (h1 : a = b)
  (h2 : x = y) :
-- imply
  a + x = b + y :=
-- proof
by
  -- Rewrite the goal using the hypotheses
  rw [h1, h2]

end algebra.eq.eq.then.eq
open algebra.eq.eq.then.eq
