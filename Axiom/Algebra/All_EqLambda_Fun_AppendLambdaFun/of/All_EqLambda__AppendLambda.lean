import Axiom.Basic


@[main]
private lemma main
  {n : ℕ}
-- given
  (h1: ∀ f : ℕ → α, Lambda (n + 1) f = append (Lambda n f) (f n)) :
-- imply
  ∀ f : ℕ → α, Lambda (n + 1) (λ i => f (i + 1)) = append (Lambda n (λ i => f (i + 1))) (f (n + 1)) := by
-- proof
  intro f
  specialize h1 (λ i => f (i + 1))
  rw [h1]


-- created on 2024-12-22
