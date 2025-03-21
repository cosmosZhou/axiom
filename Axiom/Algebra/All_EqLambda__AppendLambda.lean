import Axiom.Algebra.AppendCons.eq.Cons_Append
open Algebra


@[main]
private lemma main
  {n : ℕ} :
-- imply
  ∀ (f : ℕ → α), Lambda (n + 1) f = append (Lambda n f) (f n) := by
-- proof
  induction n with
  | zero =>
    intro f
    show Lambda (0 + 1) f = append (Lambda 0 f) (f 0)
    simp [Lambda, append]
  | succ n ih =>
  -- ih : ∀ (f : ℕ → α), Lambda (n + 1) f = append (Lambda n f) (f n)
  -- Inductive step: n = n + 1
    intro f
    show Lambda (n + 1 + 1) f = append (Lambda (n + 1) f) (f (n + 1))
    calc
      Lambda (n + 1 + 1) f = Lambda (n + 2) f := rfl
      _ = f 0 ::ᵥ Lambda (n + 1) (λ i => f (i + 1)) := by rw [Lambda]
      _ = f 0 ::ᵥ append (Lambda n (λ i => f (i + 1))) (f (n + 1)) := by rw [ih (λ i => f (i + 1))]
      _ = append (f 0 ::ᵥ Lambda n (λ i => f (i + 1))) (f (n + 1)) := by rw [AppendCons.eq.Cons_Append]
      _ = append (Lambda (n + 1) f) (f (n + 1)) := by rw [Lambda]


-- created on 2024-12-22
