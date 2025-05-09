import Mathlib.Tactic
open Lean


private def getVisibleName (name : Name) : Name :=
  match name with
  | .str prev name =>
    .str (getVisibleName prev) name
  | _ =>
    default


initialize registerBuiltinAttribute {
  name := `main
  descr := "An attribute that retrieves the file name where a declaration is defined"
  add := fun declName _stx _kind => do
    let env ← getEnv
    let some decl := env.find? declName | throwError s!"Declaration {declName} not found"
    let name := getVisibleName declName
    let mut name' :=
      match env.mainModule.components with
      | [] => panic! "a lemma must have a lean library name"
      | _ :: tail => tail.foldl .append .anonymous
    if name != `main then
      name' := name' ++ name
    addDecl <| Declaration.thmDecl {
      name := name'
      levelParams := decl.levelParams
      type := decl.type
      value := decl.value!
    }
}
