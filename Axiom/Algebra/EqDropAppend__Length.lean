import stdlib.List
import Axiom.Basic


@[main]
private lemma main
  {a b : List α} :
-- imply
  (a ++ b).drop a.length = b := by
-- proof
  induction a with
  | nil =>
    -- Base case: `a = []`
    -- `([ ] ++ b).drop [ ].length = b` by definition
    simp
  | cons x xs ih =>
    -- Inductive step: `a = x :: xs`
    -- `((x :: xs) ++ b).drop (1 + xs.length) = drop (1 + xs.length) (x :: (xs ++ b)) = drop xs.length (xs ++ b) = b` by inductive hypothesis
    simp_all [List.drop, Nat.add_comm]


-- created on 2025-05-08
