import Lean
open Lean

def compile (filePath : System.FilePath) : IO Unit := do
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
      let (_, hasNoErrors) ← Lean.Elab.runFrontend input opts fileName mainModuleName trustLevel

      if hasNoErrors then
        IO.println s!"Successfully compiled {filePath}"
      else
        IO.println s!"Errors found in {filePath}"

def compileLeanFiles (dir : System.FilePath) : IO Unit := do
  -- Initialize Lean environment
  let buildDir ← Lean.getBuildDir
  println! s!"buildDir: {buildDir}"
  let sysroot ← Lean.findSysroot
  println! s!"sysroot: {sysroot}"
  let builtinSearchPath ← Lean.getBuiltinSearchPath sysroot
  println! s!"builtinSearchPath: {builtinSearchPath}"
  let libDir ← Lean.getLibDir sysroot
  println! s!"libDir: {libDir}"

  Lean.initSearchPath sysroot [
    ".lake/build/lib",
    ".lake/packages/aesop/.lake/build/lib",
    ".lake/packages/Cli/.lake/build/lib",
    ".lake/packages/LeanSearchClient/.lake/build/lib",
    ".lake/packages/proofwidgets/.lake/build/lib",
    ".lake/packages/batteries/.lake/build/lib",
    ".lake/packages/importGraph/.lake/build/lib",
    ".lake/packages/mathlib/.lake/build/lib",
    ".lake/packages/Qq/.lake/build/lib"
  ]

  let _ ← compile (System.FilePath.mk "." / "Axiom" / "Basic.lean")

  for filePath in ← (System.FilePath.walkDir dir) do
    if filePath.extension == some "lean" then
      let _ ← compile filePath


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
