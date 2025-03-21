import Axiom.Basic

-- define the circled plus operator
class OPlus (α : Type u) where
  f : α → α → α
  associative : ∀ x y z : α, f (f x y) z = f x (f y z)

infixl:60 "⊕" => OPlus.f


-- define the circled times operator
class OTimes (α : Type u) [OPlus α] where
  f : α → α → α
  distributive : ∀ a b c : α, f (a ⊕ b) c = (f a c) ⊕ (f b c)

infixl:70 "⊗" => OTimes.f


-- define the circled dot operator, the companion operator of ⊗
class ODot (α : Type u) [OPlus α] [OTimes α] where
  f : α → α → α
  semiassociative : ∀ x y z : α, ((x ⊗ y) ⊗ z) = (x ⊗ (f y z))
  associative : ∀ x y z : α, f (f x y) z = f x (f y z)

infixl:65 "⊙" => ODot.f

-- Define the all-prefix-sums function
def all_prefix_sums [Inhabited α] [OPlus α] (a : List α) (t : α := default) : List α :=
  match a, t with
  | [], _  => []
  | a₀ :: a, sum => (sum ⊕ a₀) :: all_prefix_sums a (sum ⊕ a₀)


class Bullet (α : Type u) [OPlus α] [OTimes α] [ODot α] where
  f : α × α → α × α → α × α
  property : ∀ cᵢ c_j : α × α, f cᵢ c_j = ⟨cᵢ.fst ⊙ c_j.fst, (cᵢ.snd ⊗ c_j.fst) ⊕ c_j.snd⟩

-- define bullet operator
infixl:65 "•" => Bullet.f

-- http://shelf2.library.cmu.edu/Tech/23445461.pdf
