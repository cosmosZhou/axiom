import Axiom.Algebra.All_EqLamda__PushLamda
open Algebra


@[main]
private lemma main
  {n : ℕ}
  {f : ℕ → α} :
-- imply
  [i < n + 1] f i = ([i < n] f i).push (f n) := by
-- proof
  apply All_EqLamda__PushLamda


-- created on 2024-07-01
