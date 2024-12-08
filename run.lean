import Lean
open Lean

def compileLeanFiles (dir : System.FilePath) : IO Unit := do
  -- Initialize Lean environment
  Lean.initSearchPath (← Lean.findSysroot) [
    ".lake/packages/mathlib/.lake/build/lib",
    ".lake/build/lib"
  ]

  for filePath in ← (System.FilePath.walkDir dir) do
    if filePath.extension == some "lean" then
      IO.println s!"Compiling {filePath}"
      let input ← IO.FS.readFile filePath
      let fileName := filePath.toString
      let fileMap := Parser.mkInputContext fileName input
      let (_, _, messages) ← Parser.parseHeader fileMap
      -- Check if there are any parsing messages
      if !messages.hasErrors then
        let mainModuleName: Name := Name.mkSimple (filePath.fileStem.getD "Main")

        let opts := {}
        let trustLevel := 0

        -- Run the frontend to process the file
        let (_, hasErrors) ← Lean.Elab.runFrontend input opts fileName mainModuleName trustLevel

        if hasErrors then
          IO.println s!"Errors found in {filePath}"
        else
          IO.println s!"Successfully compiled {filePath}"


def checkTheorems (env : Environment) : IO Unit := do
  for (name, info) in env.constants.toList do
    match info with
    | ConstantInfo.thmInfo thm =>
      if thm.value.hasSorry then
        IO.println s!"Theorem {name} is unproven."
    | _ => continue


-- A script to detect unproven theorems
def isTheoremIncomplete (decl : ConstantInfo ) : MetaM Bool :=
  match decl with
  | ConstantInfo.thmInfo { value := valueExpr, .. } =>
    return valueExpr.hasSorry
  | _ => return false

def findUnprovenTheorems : MetaM (List Name) :=
  do
    let env ← getEnv
    let decls := env.constants.toList
    decls.foldlM (init := []) fun acc (name, decl) =>
      do
        if (← isTheoremIncomplete decl) then
          return name::acc
        return acc

#eval findUnprovenTheorems

def main : IO Unit := do
  let dir := System.FilePath.mk "." / "Axiom" -- Change this to the directory containing your Lean files
  compileLeanFiles dir
