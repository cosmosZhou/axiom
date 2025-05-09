import Lean

def Char.isSubscriptDigit (c : Char) : Bool :=
  c ∈ ['₀', '₁', '₂', '₃', '₄', '₅', '₆', '₇', '₈', '₉']
