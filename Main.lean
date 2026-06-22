import LeanDatalog
import Examples  -- ensures the example oleans are built & on the path for the demo

/-!
`extract [flags] <outDir> <Module.Name> [<Module.Name> ...]`

Imports the given (already-compiled) modules, reads the resulting environment,
and writes Soufflé `.facts` files for every theorem defined in those modules
(or, with `--prefix`, in every module under a namespace), together with the
transitive closure of declaration statements they depend on.
-/

open Lean LeanDatalog

/-- Parse args into (config, positionals). `--prefix P` consumes the next token. -/
partial def parseArgs : List String → Config → List String → Config × List String
  | [],                  cfg, pos => (cfg, pos.reverse)
  | "--all"    :: rest,  cfg, pos => parseArgs rest { cfg with includeAll := true } pos
  | "--values" :: rest,  cfg, pos => parseArgs rest { cfg with values := true } pos
  | "--proofs" :: rest,  cfg, pos => parseArgs rest { cfg with values := true, proofs := true } pos
  | "--no-share" :: rest, cfg, pos => parseArgs rest { cfg with noShare := true } pos
  | "--prefix" :: p :: rest, cfg, pos =>
      parseArgs rest { cfg with modulePrefixes := cfg.modulePrefixes ++ [p] } pos
  | a :: rest,           cfg, pos => parseArgs rest cfg (a :: pos)

def usage : IO Unit := do
  IO.eprintln "usage: extract [flags] <outDir> <Module.Name> [<Module.Name> ...]"
  IO.eprintln "  --all          include auto-generated theorems (eq lemmas, injEq, …)"
  IO.eprintln "  --values       encode definition/opaque bodies (decl_value + value_uses)"
  IO.eprintln "  --proofs       also encode theorem proof terms (large; implies --values)"
  IO.eprintln "  --prefix P     seed theorems from every imported module named P or P.* "
  IO.eprintln "                 (repeatable); e.g. --prefix Mathlib"
  IO.eprintln "  --no-share     reset hash-cons per declaration (bounds memory; for huge runs)"

def main (args : List String) : IO Unit := do
  let (cfg, pos) := parseArgs args {} []
  match pos with
  | outDir :: mod₀ :: rest =>
    let modules := (mod₀ :: rest).map (·.toName)
    initSearchPath (← findSysroot)
    let imports := modules.map fun m => ({ module := m } : Import)
    IO.eprintln s!"importing {modules.length} module(s)…"
    let env ← importModules imports.toArray {} (trustLevel := 1024)
    extract env modules.toArray outDir cfg
  | _ => usage; IO.Process.exit 1
