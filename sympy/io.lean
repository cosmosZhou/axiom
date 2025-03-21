import Mathlib.Tactic
open Lean

def __file__ : IO String := do
  let __file__ ← IO.Process.run {
    cmd := "sh",
    args := #["-c", "ps -o args= -p $PPID | awk '{print $3}'"],
  }
  return __file__.trimRight


def lean2ilean (filePath : System.FilePath ) : System.FilePath :=
  ".lake/build/lib" / filePath.withExtension "ilean"


def getFileMap (fileName : String) : IO FileMap :=
  -- make sure to replace \r\n with \n beforehand
  (·.toFileMap) <$> IO.FS.readFile fileName


def compile (filePath : System.FilePath) : IO (Environment × Parser.InputContext) := do
    -- IO.println s!"Compiling {filePath}"
    let input ← IO.FS.readFile filePath
    let fileName := filePath.toString
    let fileMap := Parser.mkInputContext fileName input
    let (_, _, messages) ← Parser.parseHeader fileMap
    -- Check if there are any parsing messages
    if !messages.hasErrors then
      let mainModuleName: Name := Name.mkSimple (filePath.fileStem.getD "main")
      -- println! s!"mainModuleName = {mainModuleName}"
      let opts := {}
      let trustLevel := 0
      let ileanFileName? := some (lean2ilean filePath).toString
      -- println! s!"ileanFileName? = {lean2ilean filePath}"
      -- Run the frontend to process the file
      let (env, hasNoErrors) ← Elab.runFrontend input opts fileName mainModuleName trustLevel ileanFileName?

      if hasNoErrors then
        return ⟨env, fileMap⟩
    throw $ IO.userError "Parsing error"


def exec (fn : MetaM α) : IO α := do
  let env ← importModules #[{ module := `Mathlib.Tactic }] {}
  let ((result, _), _) ← Meta.MetaM.run fn |>.toIO
    -- Create a default Core.Context
    {
      fileName := "",
      fileMap := ⟨"", #[]⟩,
    }
    -- Create a default Core.State
    { env }
  return result
