import Axiom.Algebra.Lambda.eq.AppendLambda

namespace Algebra.Eq_Lambda.Eq.to

theorem EqLambdaS
  {n : ℕ}
  {f g : ℕ → α}
-- given
  (h1 : Lambda n f = Lambda n g)
  (h2 : f n = g n) :
-- imply
  Lambda (n + 1) f = Lambda (n + 1) g := by
-- proof
  calc
    Lambda (n + 1) f = append (Lambda n f) (f n) := Lambda.eq.AppendLambda
    _ = append (Lambda n g) (g n) := by rw [h1, h2]
    _ = Lambda (n + 1) g := Lambda.eq.AppendLambda.symm


end Algebra.Eq_Lambda.Eq.to

-- created on 2024-07-01
