import stdlib.List.Vector
import Axiom.Basic


@[main]
private lemma main
  {v : List.Vector α (m * n)}
  {u : Fin m → List.Vector α n}
-- given
  (h₀ : m > 0)
  (h₁ : ∀ i : Fin m, (v.substr (i * n) n).val = (u i).val) :
-- imply
  v = ((List.Vector.range m).map fun i => u i).flatten := by
-- proof
  have h₂ : v.length = ((List.Vector.range m).map fun i => u i).flatten.length := by 
    simp [List.Vector.flatten, List.Vector.map, List.Vector.range, h₀]
  -- Use list equality to show element-wise equality
  apply List.Vector.ext
  intro j
  have := h₁ i 
  -- Decompose the index and compare elements
  -- simp_all [List.Vector.get, List.Vector.flatten, List.Vector.map, List.Vector.range, h₀, h₁]
  -- Conclude equality using the `List.ext` lemma
  sorry


-- created on 2025-05-07
