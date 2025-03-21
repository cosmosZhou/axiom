-- lake env lean --run sympy/printing/run.lean add_mul
-- lake env lean sympy/printing/run.lean
import sympy.printing.json
import sympy.io

#eval do
  let name := `Nat.modEq_iff_dvd
  let expr ← name.toExpr
  println! ← Lean.Meta.ppExpr expr
  let expr ← Expr.toExpr expr
  println! expr
  println! expr.toLatex
  println! ← Name.toJson name

def main (args : List String) : IO Unit := do
  IO.println <| ← Name.toJson args.head!.toName |> exec

#check Nat.ModEq

-- http://192.168.18.133:8000/lean/?mathlib=Nat.modEq_iff_dvd
