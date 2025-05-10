import Lemma.Algebra.Sub_Sub.eq.AddSub
open Algebra


/--
This lemma demonstrates that in an additive commutative group, the expression `a - b + c` is equivalent to `a - (b - c)`.
It leverages the group's properties to rearrange terms involving subtraction and addition, showing how inverses and associativity allow such algebraic manipulations.
-/
@[main]
private lemma main
  [AddCommGroup α]
  {a b c : α} :
-- imply
  a - b + c = a - (b - c) := by
-- proof
  rw [Sub_Sub.eq.AddSub]


-- created on 2025-03-24
-- updated on 2025-04-04
