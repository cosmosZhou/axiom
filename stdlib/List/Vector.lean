import Lemma.Algebra.LengthToList.eq.Length
import Lemma.Algebra.EqMin_SubMulS
open Algebra


class Dot (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  dot : α → β → γ

infix:71 "⬝" => Dot.dot

-- abbrev NDArray := List.Vector

namespace List.Vector

-- Implement the instance for Vector
instance : IsConstant (Vector α n) where
  is_constant v := v.val is constant


def dot [Add α] [Zero α] [Mul α] (v1 v2 : Vector α n) : α :=
  match n, v1, v2 with
  | 0, ⟨[], _⟩, ⟨[], _⟩ => 0
  | n + 1, ⟨x :: xs, h₁⟩, ⟨y :: ys, h₂⟩ =>
    have h₁ : xs.length = n := by
      simp [List.length, h₁] at h₁
      assumption
    have h₂ : ys.length = n := by
      simp [List.length, h₂] at h₂
      assumption
    x * y + dot ⟨xs, h₁⟩ ⟨ys, h₂⟩


instance [Add α] [Zero α] [Mul α] : Dot (Vector α n) (Vector α n) α := ⟨dot⟩

def sum [Add α] [Zero α] : Vector α n → α
  | ⟨v, _⟩ => v.sum

def headD : Vector α n → α → α
  | ⟨v, _⟩, d => v.headD d

def push {n : ℕ} (v : Vector α n) (x : α) : Vector α (n + 1) :=
  match n with
  | 0 => x ::ᵥ .nil
  | _ + 1 => v.head ::ᵥ (push v.tail x)

def range (n : Nat) : Vector (Fin n) n :=
  -- Use `List.range n` to generate the list of numbers from `0` to `n-1`.
  -- `List.pmap` allows mapping with a dependent function that requires a proof for each element.
  -- For each element `i` in `List.range n`, we have a proof `hi` that `i ∈ List.range n`.
  -- Using the lemma `List.mem_range`, we convert `i` to `Fin n` by proving `i < n`.
  ⟨
    List.range n |>.pmap
      (
        fun i hi =>
          ⟨i, (List.mem_range (n := n) (m := i)).mp hi⟩
      )
      (by simp),
    by simp
  ⟩

def indices (s : Slice) (n : ℕ) : Vector (Fin n) (s.length n) :=
  ⟨s.toList n, LengthToList.eq.Length (s := s) (n := n)⟩

def flatten (xs : Vector (Vector α n) m) : Vector α (m * n) :=
  ⟨(xs.toList.map Vector.toList).flatten, by rcases xs; simp_all [Function.comp_def, List.map_const']⟩

def substr (L : Vector α n) (start : Nat) (step : Nat) : Vector α (min step (n - start)) :=
  (take (step) ∘ drop start) L

def unflatten (xs : Vector α (m * n)) : Vector (Vector α n) m :=
  (range m).map fun i : Fin m => cast (by rw [EqMin_SubMulS]) (xs.substr (i * n) n)

instance [Inhabited α] : GetElem (List.Vector α n) ℕ α fun _ _ => True where
  getElem v i _ :=
    if h : i < n then
      v[(⟨i, h⟩ : Fin n)]
    else
      default

instance : HAppend (List.Vector α n) (List.Vector α m) (List.Vector α (n + m)) := ⟨List.Vector.append⟩

end List.Vector
