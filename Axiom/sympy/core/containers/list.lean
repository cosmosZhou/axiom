import Axiom.Basic

class IsConstant (T : Type v) where
  is_constant : T → Prop

-- Define the postfix operator using the type class

postfix:min "is constant" =>
  fun x => IsConstant.is_constant x

instance : IsConstant (List α) where
  is_constant : List α → Prop
    | [] => True
    | (x0 :: X) => ∀ x ∈ X, x = x0

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
