import Axiom.sympy.concrete.expr_with_limits.lambda

namespace Algebra.Lambda.eq

theorem AppendLambda
  {n : ℕ}
  {f : ℕ → α} :
-- imply
  Lambda (n + 1) f = append (Lambda n f) (f n) := by
-- proof
  apply lambda_to_append_inductive

end Algebra.Lambda.eq

-- created on 2024-07-01
