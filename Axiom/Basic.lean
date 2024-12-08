import Mathlib.Tactic

open Lean

initialize registerBuiltinAttribute {
  name  := `within
  descr := "This is my custom attribute for theorems"
  add   := fun (declName : Name) (stx : Syntax) (attrKind : AttributeKind) => do
    let env ← MonadEnv.getEnv
    let some decl := env.find? declName | throwError s!"Declaration {declName} not found"

    let declType := decl.type
    let declValue := decl.value!

    -- Extract the namespace from the attribute syntax
    let ns := match stx with
      | `(attr| within $ns:ident) => ns.getId
      | _ => default

    -- Create the new declaration name within the namespace
    let newDeclName := Name.mkStr ns declName.toString

    -- Add the declaration within the namespace
    Lean.addDecl <| Lean.Declaration.thmDecl {
      name := newDeclName
      levelParams := decl.levelParams
      type := declType
      value := declValue
    }

    IO.println s!"Attribute {attrKind} applied to {declName} with {stx}"
}
