import Mathlib.Tactic
import Axiom.sympy.concrete.expr_with_limits.lambda


namespace algebra.lambda.to.append

theorem lambda
  {n : ℕ}
  {f : ℕ → α} :
-- imply
  Lambda (n + 1) f = append (Lambda n f) (f n) :=
-- proof
by
  apply lambda_to_append_inductive

end algebra.lambda.to.append
open algebra.lambda.to.append
