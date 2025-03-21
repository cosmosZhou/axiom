import Mathlib.Tactic
import sympy.parsing.parser
import sympy.printing.latex
open Lean Elab.Tactic Meta
-- print(_.values().__iter__().__next__())


syntax (name := echo) "echo" (ident,+ <|> "*") : tactic
set_option linter.unusedVariables false

def logInfo (hypId : Name) (hypType : TacticM Lean.Expr) (goal : Bool := false) := do
  let latex := (← Expr.toExpr (← hypType)).latex_tagged hypId (if goal then "red" else"green")
  Lean.logInfo m!"{Json.compress (Json.mkObj [(toString ((← getFileMap).toPosition ((← getRef).getPos?.getD 0)).line, latex)])}"


@[tactic echo]
def evalEcho : Tactic := fun stx => do
  -- Extract the identifiers from the syntax
  withMainContext do
    let sepArgs := stx[1].getSepArgs
    for identStx in sepArgs do
      let hypId := identStx.getId
      if hypId == Name.anonymous then
        -- Print all local hypotheses
        for decl in (← getLCtx).decls do
          match decl with
          | some decl => do
            if decl.userName != `main then
              let hypType := inferType decl.toExpr
              if ← (← hypType).is_Prop  then
                logInfo decl.userName hypType
          | none =>
            continue
        -- Print the main target
        logInfo hypId getMainTarget true
      else if hypId == `main then
        if sepArgs.size > 1 then
          -- Print the main target
          logInfo hypId getMainTarget true
        else
          -- Print the all goals
          let gs ← getGoals
          for g in gs do
            let decl ← g.getDecl
            logInfo decl.userName (instantiateMVars decl.type) true
      else
        -- Print the specific local hypothesis
        logInfo hypId (inferType (← getLocalDeclFromUserName hypId).toExpr)
