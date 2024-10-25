import Mathlib.Tactic
import Axiom.algebra.lambda.to.append.lambda
set_option linter.dupNamespace false

namespace algebra.eq.eq.then.eq

theorem concat
  {n : ℕ}
  {f g : ℕ → α}
-- given
  (h1 : Lambda n f = Lambda n g)
  (h2 : f n = g n) :
-- imply
  Lambda (n + 1) f = Lambda (n + 1) g :=
-- proof
by
  calc
    Lambda (n + 1) f = append (Lambda n f) (f n) := by
      apply algebra.lambda.to.append.lambda
    _ = append (Lambda n g) (g n) := by rw [h1, h2]
    _ = Lambda (n + 1) g := by
      apply algebra.lambda.to.append.lambda.symm


end algebra.eq.eq.then.eq
open algebra.eq.eq.then.eq
