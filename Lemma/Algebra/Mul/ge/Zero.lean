import Lemma.Algebra.Mul.eq.Square
import Lemma.Algebra.Square.ge.Zero
open Algebra


@[main]
private lemma main
  [Semiring α] [LinearOrder α]
  [IsRightCancelAdd α] [ZeroLEOneClass α] [ExistsAddOfLE α]
  [PosMulMono α] [AddLeftStrictMono α]
  {a : α} :
-- imply
  a * a ≥ 0 := by
-- proof
  rw [Mul.eq.Square]
  apply Square.ge.Zero


-- created on 2024-11-29
