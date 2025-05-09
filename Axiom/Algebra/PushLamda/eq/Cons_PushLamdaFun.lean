import Axiom.Algebra.HeadLamda.eq.Fun0
import Axiom.Algebra.TailLamda.eq.LamdaFun
open Algebra


@[main]
private lemma main
  {n : ℕ}
  {f : ℕ → α} :
-- imply
  ([i < n + 1] f i).push (f (n + 1)) = f 0 ::ᵥ ([i < n] f (i + 1)).push (f (n + 1)) := calc
-- proof
  --unfold the left hand side
  ([i < n + 1] f i).push (f (n + 1)) = ([i < n + 1] f i).head ::ᵥ ([i < n + 1] f i).tail.push (f (n + 1)) := by rw [List.Vector.push]
  _ = f 0 ::ᵥ ([i < n + 1] f i).tail.push (f (n + 1)) := by simp [HeadLamda.eq.Fun0]
  _ = f 0 ::ᵥ ([i < n] f (i + 1)).push (f (n + 1)) := by simp [TailLamda.eq.LamdaFun]


-- created on 2024-12-22
