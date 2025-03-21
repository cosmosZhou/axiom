import Mathlib.Tactic
import Lean.Elab
import Lean.Expr
import Lean.PrettyPrinter
import sympy.core.containers.vector
import sympy.concrete.expr_with_limits.lambda
import std.Name
open Lean


def removeFirstToken (n : Name) : Name :=
  match n.components with
  | [] => n -- If the name has no components, return it as is
  | _ :: componentsTail => componentsTail.foldl Lean.Name.append Lean.Name.anonymous


initialize registerBuiltinAttribute {
  name := `main  -- The name of the custom attribute
  descr := "Custom attribute that retrieves the file name where a declaration is defined."
  add := fun declName _stx _kind => do
    let env ← getEnv
    let some decl := env.find? declName | throwError s!"Declaration {declName} not found"
    let name := declName.getLast
    let mut newDeclName := removeFirstToken env.mainModule
    if name != `main then
      newDeclName := newDeclName ++ name
    Lean.addDecl <| Lean.Declaration.thmDecl {
      name := newDeclName
      levelParams := decl.levelParams
      type := decl.type
      value := decl.value!
    }
}


macro "distrib" : tactic => `(tactic| with_reducible
  simp only [Nat.add_mul, Nat.mul_add, Nat.succ_mul, Nat.mul_succ]
  ac_rfl
)


class Root (α : Type _) where
  sqrt : α → α
  cubic : α → α
  quartic : α → α


notation:max (priority := 1001) "√" x:max => Root.sqrt x
notation:max "∛" x:max => Root.cubic x
notation:max "∜" x:max => Root.quartic x


noncomputable instance : Root ℝ where
  sqrt := Real.sqrt
  cubic x := x ^ (3:ℝ)⁻¹
  quartic x := x ^ (4:ℝ)⁻¹


noncomputable instance : Root ℂ where
  sqrt x := x ^ (2:ℂ)⁻¹
  cubic x := x ^ (3:ℂ)⁻¹
  quartic x := x ^ (4:ℂ)⁻¹


notation:max x "²" => x ^ 2  -- square
notation:max x "³" => x ^ 3  -- cube
notation:max x "⁴" => x ^ 4  -- tesseract


export Complex (re im normSq I arg abs)
export Real (exp cos sin arccos arcsin)
notation "π" => Real.pi
export Set (Ioo Ico Iio Icc Iic Ioc Ici Ioi univ)
export Mathlib (Vector)
export Finset (range)
export Int (fract sign)
notation:max n "is even" => Even n
notation:max n "is odd" => ¬Even n
