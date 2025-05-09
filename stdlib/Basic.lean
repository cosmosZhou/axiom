import Lean
open Lean Elab Command Parser.Term

class CtorName (α : Type u) where
  ctorName : α → String

export CtorName (ctorName)

def mkCtorName (indName : Name) : CommandElabM Unit := do
  elabCommand <| ← `(
instance : CtorName $(mkIdent indName) where
  ctorName := fun $(← (← getConstInfoInduct indName).ctors.toArray.mapM fun ctor => do
    let val := ctor.getString!
    `(matchAltExpr| | .$(mkIdent val.toName):ident $(List.replicate (← getConstInfoCtor ctor).numFields (← `(_)) |>.toArray)* => $(Syntax.mkStrLit val))
  ):matchAlt*

def $(mkIdent (indName.str "ctorName")) : $(mkIdent indName) → String := CtorName.ctorName
)


initialize
  registerDerivingHandler ``CtorName fun indNames => do
    indNames.forM mkCtorName
    return true
