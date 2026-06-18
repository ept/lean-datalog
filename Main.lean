import LeanDatalog
import Examples  -- ensures the example oleans are built & on the path for the demo

/-!
`extract <outDir> <Module.Name> [<Module.Name> ...]`

Imports the given (already-compiled) modules, reads the resulting environment,
and writes Soufflé `.facts` files for every theorem defined in those modules,
together with the transitive closure of declaration statements they depend on.
-/

open Lean LeanDatalog

def main (args : List String) : IO Unit := do
  let isFlag (s : String) := s.startsWith "--"
  let cfg : Config := {
    includeAll := args.contains "--all"
    values     := args.contains "--values" || args.contains "--proofs"
    proofs     := args.contains "--proofs"
  }
  match args.filter (!isFlag ·) with
  | outDir :: mod₀ :: rest =>
    let modules := (mod₀ :: rest).map (·.toName)
    initSearchPath (← findSysroot)
    let imports := modules.map fun m => ({ module := m } : Import)
    let env ← importModules imports.toArray {} (trustLevel := 1024)
    extract env modules.toArray outDir cfg
  | _ =>
    IO.eprintln "usage: extract [--all] [--values] [--proofs] <outDir> <Module.Name> ..."
    IO.eprintln "  --all      include auto-generated theorems (eq lemmas, injEq, …)"
    IO.eprintln "  --values   encode definition/opaque bodies (decl_value + value_uses)"
    IO.eprintln "  --proofs   also encode theorem proof terms (large; implies --values)"
    IO.Process.exit 1
