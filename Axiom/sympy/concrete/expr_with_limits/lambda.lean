import Axiom.Basic
open Mathlib

def Lambda (n : ℕ) (f : ℕ → α) : Vector α n :=
  match n with
  | 0 => Vector.nil
  | n + 1 => f 0 ::ᵥ (Lambda n (λ i => f (i + 1)))


def append {n : ℕ} (v : Vector α n) (x : α) : Vector α (n + 1) :=
  match n with
  | 0 => x ::ᵥ Vector.nil
  | _ + 1 => v.head ::ᵥ (append v.tail x)


lemma append_to_cons
  {n : ℕ}
  {x y : α}
  (v : Vector α n) :
-- imply
  append (Vector.cons x v) y = Vector.cons x (append v y) := by
-- proof
  induction n with
  | zero =>
    rfl
  | succ n _ =>
    rfl


@[simp]
lemma simp_Lambda_head
  {n : ℕ}
  {f : ℕ → α} :
-- imply
  (Lambda (n + 1) f).head = f 0 := by
-- proof
  rw [Lambda]
  rfl


@[simp]
lemma simp_Lambda_tail
  {n : ℕ}
  {f : ℕ → α} :
-- imply
  (Lambda (n + 1) f).tail = Lambda n (λ i => f (i + 1)) := by
-- proof
  rw [Lambda]
  rfl


lemma append_lambda_to_cons
  (n : ℕ)
  (f : ℕ → α) :
-- proof
  append (Lambda (n + 1) f) (f (n + 1)) =
  f 0 ::ᵥ (append (Lambda n (λ i => f (i + 1))) (f (n + 1))) := by
  --unfold the left hand side
  calc
    append (Lambda (n + 1) f) (f (n + 1)) = (Lambda (n + 1) f).head ::ᵥ (append (Lambda (n + 1) f).tail (f (n + 1))) := by rw [append]
    _ = f 0 ::ᵥ (append (Lambda (n + 1) f).tail (f (n + 1))) := by simp
    _ = f 0 ::ᵥ (append (Lambda n (λ i => f (i + 1))) (f (n + 1))) := by simp


lemma substitution_step
  {n : ℕ}
-- given
  (h1: ∀ f : ℕ → α, Lambda (n + 1) f = append (Lambda n f) (f n)) :
-- imply
  ∀ f : ℕ → α, Lambda (n + 1) (λ i => f (i + 1)) = append (Lambda n (λ i => f (i + 1))) (f (n + 1)) := by
-- proof
  intro f
  specialize h1 (λ i => f (i + 1))
  rw [h1]


lemma lambda_to_append_inductive
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
      _ = append (f 0 ::ᵥ Lambda n (λ i => f (i + 1))) (f (n + 1)) := by rw [append_to_cons]
      _ = append (Lambda (n + 1) f) (f (n + 1)) := by rw [Lambda]
