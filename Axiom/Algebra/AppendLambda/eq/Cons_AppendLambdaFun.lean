import Axiom.Algebra.HeadLambda.eq.Fun0
import Axiom.Algebra.TailLambda.eq.LambdaFun
open Algebra


@[main]
private lemma main
  {n : ℕ}
  {f : ℕ → α} :
-- imply
  append (Lambda (n + 1) f) (f (n + 1)) = f 0 ::ᵥ (append (Lambda n (λ i => f (i + 1))) (f (n + 1))) := calc
-- proof
  --unfold the left hand side
  append (Lambda (n + 1) f) (f (n + 1)) = (Lambda (n + 1) f).head ::ᵥ (append (Lambda (n + 1) f).tail (f (n + 1))) := by rw [append]
  _ = f 0 ::ᵥ (append (Lambda (n + 1) f).tail (f (n + 1))) := by simp [HeadLambda.eq.Fun0]
  _ = f 0 ::ᵥ (append (Lambda n (λ i => f (i + 1))) (f (n + 1))) := by simp [TailLambda.eq.LambdaFun]


-- created on 2024-12-22
