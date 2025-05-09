import Axiom.Algebra.Lamda.eq.PushLamda
open Algebra


@[main]
private lemma main
  {n : ℕ}
  {f g : ℕ → α}
-- given
  (h₀ : [i < n] f i = [i < n] g i)
  (h₁ : f n = g n) :
-- imply
  [i < n + 1] f i = [i < n + 1] g i := calc
-- proof
  [i < n + 1] f i = ([i < n] f i).push (f n) := Lamda.eq.PushLamda
  _ = ([i < n] g i).push (g n) := by rw [h₀, h₁]
  _ = [i < n + 1] g i := Lamda.eq.PushLamda.symm


-- created on 2024-07-01
