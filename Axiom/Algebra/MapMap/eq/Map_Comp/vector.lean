import Axiom.Algebra.MapMap.eq.Map_Comp
import Axiom.Algebra.Eq.of.EqValS
open Mathlib Algebra


@[main]
private lemma main
  (g : β → γ)
  (f : α → β)
  (l : Vector α n) :
-- imply
  (l.map f).map g = l.map (g ∘ f) := by
-- proof
  let v1 : Vector γ n := ⟨(l.val.map f).map g, by simp⟩
  let v2 : Vector γ n := ⟨l.val.map (g ∘ f), by simp⟩
  have h_eq : v1 = v2 :=
    Eq.of.EqValS (MapMap.eq.Map_Comp g f l.val)
  have h_eq1 : v1 = (l.map f).map g := by
    rfl
  have h_eq2 : v2 = l.map (g ∘ f) := by
    rfl
  rw [h_eq1.symm, h_eq2.symm, h_eq]


-- created on 2024-07-01
