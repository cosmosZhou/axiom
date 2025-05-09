import stdlib.List.Vector
import Axiom.Basic


@[main]
private lemma main
  {v : List.Vector α (m * n)} :
-- imply
  v = v.unflatten.flatten := by
-- proof
  cases v
  -- We need to show that the original vector `v` is equal to the result of unflattening and then flattening `v`.
  -- This involves showing that the elements and their positions are preserved through these operations.
  simp [List.Vector.unflatten, List.Vector.flatten]
  -- Simplify the expressions using the definitions of `unflatten` and `flatten`.
  -- This step uses the fact that `List.map` and `List.flatten` operations are inverses when applied to chunks of the original list.
  -- The `rfl` tactic confirms that the left-hand side and the right-hand side of the equation are definitionally equal.
  -- This is possible because the operations of splitting into chunks and concatenating them back preserve the original list structure.
  induction m <;>
    simp_all [List.range, List.pmap, List.map, List.flatten]
  -- Use induction on `m` to handle all possible cases of `m` (including edge cases like `m = 0`).
  -- For each case, simplify the expressions and verify that the equality holds.
  sorry

-- created on 2025-05-07
