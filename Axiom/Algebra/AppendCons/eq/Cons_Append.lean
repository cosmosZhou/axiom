import Axiom.Basic


@[main]
private lemma main
  {n : ℕ}
  {x y : α}
  {v : Vector α n} :
-- imply
  append (x ::ᵥ v) y = x ::ᵥ append v y := by
-- proof
  induction n <;> rfl


-- created on 2024-12-22
