import stdlib.Basic
import stdlib.String
open Lean

def Lean.Name.head (name : Name) : Name :=
  name.components.headD anonymous

def Lean.Name.get (name : Name) (i : Nat): Name :=
  name.components.getD i anonymous

def Lean.Name.getLast (name : Name) : Name :=
  match name with
  | str _ s => s.toName
  | _ => anonymous

def Lean.Name.normalized (name : Name) : Name :=
  if name == anonymous then
    `main
  else
    let components := name.components
    if let some (.succ index) := components.idxOf? `«_@» then
      if h : index < components.length then
        let last := components[index]
        let last := last.toString ++ "✝"
        let pre := (components.take index).foldl (fun acc n => acc ++ n) .anonymous
        .str pre last
      else
        name
    else
      name

def Lean.Name.escape_specials (name : Name) (sep : String) : String :=
  sep.intercalate (name.normalized.components.map (·.toString.escape_specials))

def Lean.Name.toConstantInfo (name : Name) : MetaM ConstantInfo := do
  -- Check if the constant exists in the environment
  if (← getEnv).contains name then
    getConstInfo name
  else
    throwError s!"Constant {name} not found"

def Lean.Name.toExpr (name : Name) : MetaM Expr := do
  (·.type) <$> name.toConstantInfo
  -- name.toConstantInfo >>= fun info => return info.type


#eval mkCtorName ``Lean.Name
