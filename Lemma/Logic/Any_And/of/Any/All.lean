import sympy.concrete.quantifier
import Lemma.Basic


@[main]
private lemma main
  {p q r : α → Prop}
-- given
  (h₀ : ∀ x, p x)
  (h₁ : ∃ x | r x, q x) :
-- imply
  ∃ x | r x, p x ∧ q x := by
-- proof
  let ⟨x, h_q', h_p'⟩ := h₁
  have h₀ := h₀ x
  use x


-- created on 2025-05-01
