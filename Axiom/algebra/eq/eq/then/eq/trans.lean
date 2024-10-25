namespace algebra.eq.eq.then.eq

theorem trans
  {α : Type _}
  {a b x : α}
-- given
  (h1 : b = x)
  (h2 : x = a) :
-- imply
  b = a :=
-- proof
by
  apply Eq.trans h1 h2

end algebra.eq.eq.then.eq
open algebra.eq.eq.then.eq
