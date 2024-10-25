namespace algebra.eq.eq.then.eq


theorem sub
  {α : Type _} [Sub α]
  {a b x y : α}
-- given
  (h1 : a = b)
  (h2 : x = y) :
-- imply
  a - x = b - y :=
-- proof
by
  rw [h1, h2]

end algebra.eq.eq.then.eq
open algebra.eq.eq.then.eq
