import Mathlib.Tactic

class IsUniform (α : Type u) [DecidableEq α] (T : Type v) where
  is_uniform : T → Prop

-- Define the postfix operator using the type class

postfix:min "is uniform" =>
  fun x => IsUniform.is_uniform x

instance [DecidableEq α] : IsUniform α (List α) where
  is_uniform := fun xs =>
    match xs with
    | [] => True
    | (x :: xs) => ∀ y ∈ xs, y = x

namespace List

def arange (n : Nat) : List (Fin n) :=
  have h : n <= n := by rfl
  loop n [] h
where
  loop (k : Nat) (ns : List (Fin n)) (h : k <= n) : List (Fin n) :=
  match k with
  | 0   => ns
  | i + 1 =>
    have h' : i < n := by
      apply Nat.lt_of_lt_of_le (Nat.lt_succ_self i) h
    have h'' : i <= n := by
      apply Nat.le_of_lt h'
    loop i (⟨i, h'⟩ :: ns) h''


def substr (start : Nat) (step : Nat) : List α → List α :=
  take (step) ∘ drop start


end List
