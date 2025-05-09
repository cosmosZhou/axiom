import Axiom.Algebra.FDiv.eq.FloorDiv
import Axiom.Algebra.DivAdd.eq.Add1Div
import Axiom.Algebra.CoeAdd.eq.AddCoeS
import Axiom.Algebra.FloorAdd1.eq.Add1Floor
open Algebra


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d ≠ 0) :
-- imply
  (d + n) // d = 1 + n // d := by
-- proof
  rw [FDiv.eq.FloorDiv]
  rw [FDiv.eq.FloorDiv]
  rw [CoeAdd.eq.AddCoeS.int]
  rw [DivAdd.eq.Add1Div (by simp [h] : (d : ℚ) ≠ 0)]
  -- Apply the property of the floor function for adding an integer
  rw [FloorAdd1.eq.Add1Floor]


-- created on 2025-03-21
-- updated on 2025-04-20
