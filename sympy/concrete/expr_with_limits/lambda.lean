import Mathlib.Tactic
open Mathlib

def Lambda (n : ℕ) (f : ℕ → α) : Vector α n :=
  match n with
  | 0 => Vector.nil
  | n + 1 => f 0 ::ᵥ (Lambda n (λ i => f (i + 1)))


def append {n : ℕ} (v : Vector α n) (x : α) : Vector α (n + 1) :=
  match n with
  | 0 => x ::ᵥ Vector.nil
  | _ + 1 => v.head ::ᵥ (append v.tail x)
