import Axiom.Basic


@[main]
private lemma main
  {s : List α}
  {x₀ : α}
-- given
  (h: ∀ x ∈ s, x = x₀) :
-- imply
  s is constant := by
-- proof
  cases s with
  | nil =>
    simp [IsConstant.is_constant]
  | cons x s =>
    simp [IsConstant.is_constant] at h
    intro t t_in_s
    have h1 : x = x₀ := h.left
    have h2 : ∀ a ∈ s, a = x₀ := h.right
-- Use the universal quantifier to get `t = x₀`
    have h3 : t = x₀ := h2 t t_in_s
    rw [h1, h3]


-- created on 2024-07-01
