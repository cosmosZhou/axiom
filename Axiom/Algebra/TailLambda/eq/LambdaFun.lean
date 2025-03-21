import Axiom.Basic


@[main]
private lemma main
  {n : ℕ}
  {f : ℕ → α} :
-- imply
  (Lambda (n + 1) f).tail = Lambda n (λ i => f (i + 1)) := by
-- proof
  rw [Lambda]
  rfl


-- created on 2024-12-22
