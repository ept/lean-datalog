# lean-datalog

Extract the **statements of theorems proved in a Lean 4 run** as syntax trees,
encode them in **relational form**, and query them with **Datalog in Soufflé** —
without modifying the Lean compiler and without parsing source text.

Statements are captured as fully-elaborated kernel terms (`Expr`), read straight
from the compiled `Environment`. So notation is expanded, names are fully
qualified, implicit arguments and universe levels are explicit, and two
statements that are equal-up-to-elaboration encode identically.

## How it works

1. `lake build` compiles your project to `.olean` files as usual.
2. `lake exe extract <outDir> <Module> …` imports those modules (via
   `Lean.importModules`), reads the resulting `Environment`, and:
   - finds every `theorem` **defined in the target modules** — the set proved in
     this run (`target_theorem`);
   - encodes each theorem's *type* (its statement) as a tree of facts;
   - transitively encodes the *types* of every declaration the statements
     reference, with `depends_on` edges.
3. Point Soufflé at the fact directory and run Datalog queries.

By default only **types/statements** are encoded. Definition bodies and theorem
proof terms can be added with `--values` / `--proofs` (see below).

## Layout

```
LeanDatalog/Basic.lean      Expr/Level → relational facts (hash-consed)
LeanDatalog/Frontend.lean   env → target theorems + dependency closure
Main.lean                   the `extract` executable
Examples/Sample.lean        demo theorems
souffle/schema.dl           relation declarations + .input directives
souffle/queries.dl          derived views + example structural queries
```

## Quick start

```bash
# build the tool and the example library
lake build

# extract every theorem in Examples.Sample (+ statement deps) into ./out
lake exe extract out Examples.Sample
#   --all      also include auto-generated lemmas (eq_1, injEq, sizeOf_spec, …)
#   --values   also encode definition/opaque *bodies*    (decl_value + value_uses)
#   --proofs   also encode theorem *proof terms*  (implies --values; see caveat)

# run the example queries; results land in ./results/*.csv
mkdir -p results
souffle -F out -D results souffle/queries.dl
```

Run it on your own code by passing your module names, e.g.
`lake exe extract out My.Module.A My.Module.B`. The tool must be able to import
those modules, so either add them as a dependency of this Lake package, or run
the executable with `LEAN_PATH` pointing at their build output.

## The relational encoding

Every `Expr`/`Level` subterm gets a globally-unique integer **node id**.
**Structurally-equal subterms share one id** (hash-consing), so "these two
statements mention the same subterm" is just id equality, and storage stays
compact at scale.

Declaration-level relations:

| relation | meaning |
|---|---|
| `decl(name, kind, root)` | `kind` ∈ theorem/def/axiom/inductive/ctor/recursor/…; `root` = node id of its type |
| `target_theorem(name)` | theorems defined in the analysed modules |
| `depends_on(name, dep)` | `name`'s **statement** references constant `dep` |
| `decl_value(name, root)` | node id of `name`'s **value** (def body / proof term); only with `--values`/`--proofs` |
| `value_uses(name, dep)` | `name`'s **value** references constant `dep`; only with `--values`/`--proofs` |

Expression nodes (`expr_node(id, kind)` tags each; payload relations carry the
fields) mirror Lean's `Expr` constructors one-to-one:

`expr_app(id, fn, arg)` · `expr_const(id, name)` +
`expr_const_level(id, pos, level)` · `expr_bvar(id, idx)` ·
`expr_sort(id, level)` · `expr_lam/expr_forall(id, binder, type, body, info)` ·
`expr_let(id, name, type, value, body)` · `expr_lit_nat/expr_lit_str(id, val)` ·
`expr_mdata(id, inner)` · `expr_proj(id, typeName, idx, struct)` ·
`expr_fvar/expr_mvar(id, name)`.

Universe levels are encoded the same way: `level_node(id, kind)` plus
`level_succ`, `level_max`, `level_imax`, `level_param`.

`souffle/queries.dl` builds reusable views on top — `child`/`subterm`
(structural containment), `strip_foralls` (peel binders to the conclusion),
`head` (application-spine head), `thm_conclusion`, `thm_mentions`, and `reaches`
(transitive dependency closure) — then shows six example searches:

- equational theorems (conclusion head is `Eq`)
- theorems mentioning addition (`HAdd.hAdd`)
- theorems mentioning a user type (`Examples.Tree`)
- theorems transitively depending on a declaration
- universe-polymorphic theorems
- theorems containing a numeric literal (and its value)

## Semantics worth knowing

- **Statements vs. values.** By default `depends_on`/`reaches` follow constants
  in *statements* only. `add_comm_nat`'s statement mentions
  `HAdd.hAdd`/`instAddNat` but **not** `Nat.add` — the latter lives in
  `instAddNat`'s *value*. Pass `--values` and `Nat.add` shows up: encoding a
  value also chases the constants it references (`value_uses`), so the closure
  closes over them. Use `uses`/`reaches_any` in queries for the combined graph.
- **Proof blowup.** `--proofs` encodes theorem proof terms and chases *their*
  references — i.e. the full transitive proof forest. On the 6-theorem example
  this grows the export from ~180 nodes to ~72k (3 MB). It is correct and
  complete, but at Mathlib scale it is very large; shard by module or prefer
  `--values` unless you specifically need proof structure.
- **de Bruijn indices.** Bound variables are `expr_bvar(id, idx)`; binders are
  un-named-but-recorded on `expr_lam`/`expr_forall`. Alpha-equivalent terms are
  therefore structurally identical (and share ids).
- **Auto-generated theorems** (equation lemmas, `injEq`, `sizeOf_spec`, …) are
  filtered out of the seed set by default; pass `--all` to keep them.

## Scaling to Mathlib

The encoding is built for it. Validated on `Init.Data.List.Lemmas`: 681
theorems, 929 declarations, 12k distinct expr nodes extracted in ~0.2s, all six
queries in ~0.1s, 748 KB of facts — hash-consing does the heavy lifting.

For a full Mathlib run: build Mathlib, then pass the module list to `extract`
(facts stream to disk, so memory stays bounded by the hash-cons tables). The
node-id space is `number` (64-bit, as built here). For very large corpora,
shard by target module into separate fact dirs, or load facts into Soufflé's
SQLite backend instead of TSV.

## Extending

- **Name structure for prefix queries:** emit a `name_prefix(name, prefix)`
  relation, or split `Name` into components, instead of treating names as opaque
  symbols.
- **Surface syntax too:** the same streaming/hash-cons machinery works on
  `Syntax`; add a parallel `syn_*` family if you also want the un-elaborated
  parse tree.

## Requirements

- Lean toolchain `leanprover/lean4:v4.31.0` (pinned in `lean-toolchain`).
- Soufflé ≥ 2.5 (`souffle` on `PATH`).
