import Mathlib.Tactic


class IntegerRing (Z : Type) extends LinearOrderedSemiring Z, Sub Z, Div Z, Mod Z where
  succ_le_of_lt {a b : Z} : a < b → a + 1 ≤ b
  lt_of_succ_le {a b : Z} : a + 1 ≤ b → a < b
  lt_succ_of_le {a b : Z} : a ≤ b → a < b + 1
  le_pred_of_lt {a b : Z} : a < b → a ≤ b - 1
  div_add_mod {n d : Z} : n = n / d * d + n % d
  add_sub_cancel (a b : Z) : a + b - b = a


instance : IntegerRing Nat where
  succ_le_of_lt := Nat.succ_le_of_lt
  lt_of_succ_le := Nat.lt_of_succ_le
  lt_succ_of_le := Nat.lt_succ_of_le
  le_pred_of_lt := Nat.le_pred_of_lt
  div_add_mod {n d : Nat} := by
    rw [Nat.mul_comm]
    apply Eq.symm
    apply Nat.div_add_mod n d
  add_sub_cancel := Nat.add_sub_cancel


instance : IntegerRing Int where
  succ_le_of_lt := Int.add_one_le_of_lt
  lt_of_succ_le := Int.lt_of_add_one_le
  lt_succ_of_le := Int.lt_add_one_of_le
  le_pred_of_lt := Int.le_sub_one_of_lt
  div_add_mod {n d : Int} := by
    apply Eq.symm
    rw [Int.add_comm]
    rw [Int.mul_comm]
    apply Int.emod_add_ediv
  add_sub_cancel := Int.add_sub_cancel
