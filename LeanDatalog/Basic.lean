import Lean

/-!
# Relational encoding of Lean `Expr`s for Soufflé Datalog

Each `Expr` and `Level` subterm is assigned a globally-unique integer node id.
Structurally-equal subterms are hash-consed to the *same* id, so common
sub-expressions are shared (important at Mathlib scale, and it makes
"these two statements mention the same subterm" a trivial id equality in Datalog).

We stream one tab-separated `<relation>.facts` file per relation into an output
directory. Soufflé reads these directly via `.input` directives.

The relation schema is documented in `souffle/schema.dl`.
-/

namespace LeanDatalog

open Lean

/-- Mutable extraction state: id allocator, hash-cons tables, open file handles. -/
structure State where
  dir       : System.FilePath
  nextId    : Nat := 0
  exprIds   : Std.HashMap Expr Nat := {}
  levelIds  : Std.HashMap Level Nat := {}
  handles   : Std.HashMap String IO.FS.Handle := {}

abbrev EncM := StateRefT State IO

/-- Allocate a fresh globally-unique node id. -/
def freshId : EncM Nat :=
  modifyGet fun s => (s.nextId, { s with nextId := s.nextId + 1 })

/-- Lazily open (truncating) and cache one file handle per relation. -/
def getHandle (rel : String) : EncM IO.FS.Handle := do
  match (← get).handles[rel]? with
  | some h => return h
  | none =>
    let path := (← get).dir / s!"{rel}.facts"
    let h ← IO.FS.Handle.mk path IO.FS.Mode.write
    modify fun s => { s with handles := s.handles.insert rel h }
    return h

/-- Emit one fact (a row of tab-separated columns) into relation `rel`. -/
def emit (rel : String) (cols : Array String) : EncM Unit := do
  let h ← getHandle rel
  h.putStr (String.intercalate "\t" cols.toList)
  h.putStr "\n"

/-- Soufflé fact files are TSV; defend against stray tabs/newlines in symbols. -/
def sanitize (s : String) : String :=
  s.replace "\t" " " |>.replace "\n" " " |>.replace "\r" " "

def nm (n : Name) : String := sanitize n.toString

def binderInfoStr : BinderInfo → String
  | .default        => "default"
  | .implicit       => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit   => "instImplicit"

/-- Encode a universe `Level` as a tree of facts, returning its node id. -/
partial def encodeLevel (l : Level) : EncM Nat := do
  if let some id := (← get).levelIds[l]? then return id
  let id ← match l with
    | .zero       => do
        let id ← freshId; emit "level_node" #[toString id, "zero"]; pure id
    | .succ p     => do
        let pId ← encodeLevel p
        let id ← freshId
        emit "level_node" #[toString id, "succ"]
        emit "level_succ" #[toString id, toString pId]
        pure id
    | .max a b    => do
        let aId ← encodeLevel a; let bId ← encodeLevel b
        let id ← freshId
        emit "level_node" #[toString id, "max"]
        emit "level_max" #[toString id, toString aId, toString bId]
        pure id
    | .imax a b   => do
        let aId ← encodeLevel a; let bId ← encodeLevel b
        let id ← freshId
        emit "level_node" #[toString id, "imax"]
        emit "level_imax" #[toString id, toString aId, toString bId]
        pure id
    | .param n    => do
        let id ← freshId
        emit "level_node" #[toString id, "param"]
        emit "level_param" #[toString id, nm n]
        pure id
    | .mvar _     => do
        let id ← freshId; emit "level_node" #[toString id, "mvar"]; pure id
  modify fun s => { s with levelIds := s.levelIds.insert l id }
  return id

/-- Encode an `Expr` as a tree of facts, returning its (hash-consed) node id. -/
partial def encodeExpr (e : Expr) : EncM Nat := do
  if let some id := (← get).exprIds[e]? then return id
  let id ← match e with
    | .bvar i => do
        let id ← freshId
        emit "expr_node" #[toString id, "bvar"]
        emit "expr_bvar" #[toString id, toString i]
        pure id
    | .fvar fv => do
        let id ← freshId
        emit "expr_node" #[toString id, "fvar"]
        emit "expr_fvar" #[toString id, nm fv.name]
        pure id
    | .mvar mv => do
        let id ← freshId
        emit "expr_node" #[toString id, "mvar"]
        emit "expr_mvar" #[toString id, nm mv.name]
        pure id
    | .sort u => do
        let uId ← encodeLevel u
        let id ← freshId
        emit "expr_node" #[toString id, "sort"]
        emit "expr_sort" #[toString id, toString uId]
        pure id
    | .const n us => do
        let id ← freshId
        emit "expr_node" #[toString id, "const"]
        emit "expr_const" #[toString id, nm n]
        for h : i in [0:us.length] do
          let uId ← encodeLevel us[i]
          emit "expr_const_level" #[toString id, toString i, toString uId]
        pure id
    | .app f a => do
        let fId ← encodeExpr f
        let aId ← encodeExpr a
        let id ← freshId
        emit "expr_node" #[toString id, "app"]
        emit "expr_app" #[toString id, toString fId, toString aId]
        pure id
    | .lam bn bt body bi => do
        let btId ← encodeExpr bt
        let bodyId ← encodeExpr body
        let id ← freshId
        emit "expr_node" #[toString id, "lam"]
        emit "expr_lam" #[toString id, nm bn, toString btId, toString bodyId, binderInfoStr bi]
        pure id
    | .forallE bn bt body bi => do
        let btId ← encodeExpr bt
        let bodyId ← encodeExpr body
        let id ← freshId
        emit "expr_node" #[toString id, "forall"]
        emit "expr_forall" #[toString id, nm bn, toString btId, toString bodyId, binderInfoStr bi]
        pure id
    | .letE dn t v body _ => do
        let tId ← encodeExpr t
        let vId ← encodeExpr v
        let bodyId ← encodeExpr body
        let id ← freshId
        emit "expr_node" #[toString id, "let"]
        emit "expr_let" #[toString id, nm dn, toString tId, toString vId, toString bodyId]
        pure id
    | .lit (.natVal v) => do
        let id ← freshId
        emit "expr_node" #[toString id, "lit_nat"]
        emit "expr_lit_nat" #[toString id, toString v]
        pure id
    | .lit (.strVal v) => do
        let id ← freshId
        emit "expr_node" #[toString id, "lit_str"]
        emit "expr_lit_str" #[toString id, sanitize v]
        pure id
    | .mdata _ inner => do
        let iId ← encodeExpr inner
        let id ← freshId
        emit "expr_node" #[toString id, "mdata"]
        emit "expr_mdata" #[toString id, toString iId]
        pure id
    | .proj tn idx s => do
        let sId ← encodeExpr s
        let id ← freshId
        emit "expr_node" #[toString id, "proj"]
        emit "expr_proj" #[toString id, nm tn, toString idx, toString sId]
        pure id
  modify fun s => { s with exprIds := s.exprIds.insert e id }
  return id

/-- A short tag for the kind of a constant. -/
def constKind : ConstantInfo → String
  | .axiomInfo _   => "axiom"
  | .defnInfo _    => "def"
  | .thmInfo _     => "theorem"
  | .opaqueInfo _  => "opaque"
  | .quotInfo _    => "quot"
  | .inductInfo _  => "inductive"
  | .ctorInfo _    => "ctor"
  | .recInfo _     => "recursor"

end LeanDatalog
