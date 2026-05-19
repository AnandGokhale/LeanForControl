import Batteries.Tactic.Lint
import Batteries.Data.Array.Basic
import Lake.CLI.Main

open Lean Core Elab Command Batteries.Tactic.Lint
open System (FilePath)

abbrev NoLints := Array (Name × Name)

def readJsonFile (α) [FromJson α] (path : System.FilePath) : IO α := do
  let _ : MonadExceptOf String IO := ⟨throw ∘ IO.userError, fun x _ => x⟩
  liftExcept <| fromJson? <|← liftExcept <| Json.parse <|← IO.FS.readFile path

def writeJsonFile [ToJson α] (path : System.FilePath) (a : α) : IO Unit :=
  IO.FS.writeFile path <| toJson a |>.pretty.push '\n'

open Lake

def resolveDefaultRootModules : IO (Array Name) := do
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let config ← MonadError.runEIO <| mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
  let some workspace ← loadWorkspace config |>.toBaseIO
    | throw <| IO.userError "failed to load Lake workspace"
  let defaultTargetModules := workspace.root.defaultTargets.flatMap fun target =>
    if let some lib := workspace.root.findLeanLib? target then
      lib.roots
    else if let some exe := workspace.root.findLeanExe? target then
      #[exe.config.root]
    else
      #[]
  return defaultTargetModules

structure LinterConfig where
  updateNoLints : Bool := false
  noBuild : Bool := false
  trace := false

@[always_inline, inline]
private def Except.consError (e : ε) : Except (List ε) α → Except (List ε) α
  | Except.error errs => Except.error <| e :: errs
  | Except.ok _       => Except.error [e]

def parseLinterArgs (args : List String) :
    Except (List String) (LinterConfig × List Name) :=
  go {} [] args
where
  go (parsed : LinterConfig) (mods: List Name) : List String → Except (List String) (LinterConfig × List Name)
    | arg :: rest =>
      if let some parsed := parseArg parsed arg then
        go parsed mods rest
      else
        match arg.toName with
        | .anonymous => Except.error [s!"could not parse argument '{arg}'"]
        | mod => go parsed (mod :: mods) rest
    | [] => Except.ok (parsed, mods.reverse)
  parseArg (parsed : LinterConfig) : String → Option LinterConfig
    | "--update"   => some { parsed with updateNoLints := true }
    | "--no-build" => some { parsed with noBuild := true }
    | "--trace"
    | "-v"         => some { parsed with trace := true }
    | _ => none

def determineModulesToLint (specifiedModules : List Name) : IO (Array Name) := do
  match specifiedModules with
  | [] =>
    println!"Automatically detecting modules to lint"
    let defaultModules ← resolveDefaultRootModules
    println!"Default modules: {defaultModules}"
    return defaultModules
  | modules =>
    println!"Running linter on specified modules: {modules}"
    return modules.toArray

unsafe def runLinterOnModule (cfg : LinterConfig) (module : Name) : IO Unit := do
  let { updateNoLints, noBuild, trace } := cfg
  initSearchPath (← findSysroot)
  let rec
    buildIfNeeded (module : Name) : IO Unit := do
      let olean ← findOLean module
      unless (← olean.pathExists) do
        if noBuild then
          IO.eprintln s!"[{module}] Could not find olean for module `{module}`"
          IO.Process.exit 1
        else
          let child ← IO.Process.spawn {
            cmd := (← IO.getEnv "LAKE").getD "lake"
            args := #["build", s!"+{module}"]
            stdin := .null
          }
          _ ← child.wait
  buildIfNeeded module
  let lintModule := `Batteries.Tactic.Lint
  buildIfNeeded lintModule
  let nolintsFile : FilePath := "scripts/nolints.json"
  let nolints ← if ← nolintsFile.pathExists then
    readJsonFile NoLints nolintsFile
  else
    pure #[]
  unsafe Lean.enableInitializersExecution
  let env ← importModules #[module, lintModule] {} (trustLevel := 1024) (loadExts := true)
  let mut opts : Options := {}
  if trace then
    opts := opts.setBool `trace.Batteries.Lint true
  let ctx := { fileName := "", fileMap := default, options := opts }
  let state := { env }
  Prod.fst <$> (CoreM.toIO · ctx state) do
    traceLint s!"Starting lint..." (inIO := true) (currentModule := module)
    let decls ← getDeclsInPackage module.getRoot
    let linters ← getChecks (slow := true) (runAlways := none) (runOnly := none)
    let results ← lintCore decls linters (inIO := true) (currentModule := module)
    if updateNoLints then
      writeJsonFile (α := NoLints) nolintsFile <|
        .qsort (lt := fun (a, b) (c, d) => a.lt c || (a == c && b.lt d)) <|
        .flatten <| results.map fun (linter, decls) =>
        decls.fold (fun res decl _ => res.push (linter.name, decl)) #[]
    let results := results.map fun (linter, decls) =>
      .mk linter <| nolints.foldl (init := decls) fun decls (linter', decl') =>
        if linter.name == linter' then decls.erase decl' else decls
    let failed := results.any (!·.2.isEmpty)
    if failed then
      let fmtResults ←
        formatLinterResults results decls (groupByFilename := true) (useErrorFormat := true)
          s!"in {module}" (runSlowLinters := true) .medium linters.size
      IO.print (← fmtResults.toString)
      IO.Process.exit 1
    else
      IO.println s!"-- Linting passed for {module}."

unsafe def main (args : List String) : IO Unit := do
  let (cfg, mods) ← match parseLinterArgs args with
    | Except.ok args => pure args
    | Except.error msgs => do
      IO.eprintln s!"Error parsing args:\n  {"\n  ".intercalate msgs}"
      IO.Process.exit 1
  let modulesToLint ← determineModulesToLint mods
  modulesToLint.forM <| runLinterOnModule cfg
  IO.Process.exit 0
