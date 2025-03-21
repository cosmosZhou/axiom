import Axiom.Algebra.All_EqLambda__AppendLambda


@[main]
private lemma main
  {n : ℕ}
  {f : ℕ → α} :
-- imply
  Lambda (n + 1) f = append (Lambda n f) (f n) := by
-- proof
  apply Algebra.All_EqLambda__AppendLambda


-- created on 2024-07-01
