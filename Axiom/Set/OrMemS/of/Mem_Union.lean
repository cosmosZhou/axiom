import Axiom.Basic


@[main]
private lemma finset
  [DecidableEq ι]
  {A B : Finset ι}
  {e : ι}
-- given
  (h : e ∈ A ∪ B) :
-- imply
  e ∈ A ∨ e ∈ B := by
-- proof
   -- Rewrite the hypothesis `h` using the definition of union membership.
  rw [Finset.mem_union] at h
    -- After rewriting, `h` is exactly the goal, so we can conclude the proof by exacting `h`.
  exact h


@[main]
private lemma main
  {A B : Set α}
  {e : α}
-- given
  (h : e ∈ A ∪ B) :
-- imply
  e ∈ A ∨ e ∈ B := by
-- proof
   -- Rewrite the hypothesis `h` using the definition of union membership.
  rw [Set.mem_union] at h
    -- After rewriting, `h` is exactly the goal, so we can conclude the proof by exacting `h`.
  exact h


-- created on 2025-04-30
