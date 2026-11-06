/-
Copyright (c) 2026 Patrick Elliott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Elliott
-/
import Lean

/-!
# Statement closures

`scripts/checks.py` records human checks that Lean declarations state what a source says. A check
covers a declaration's statement closure: its type and docstring, and every declaration of the
project that the statement mentions, followed through the bodies of definitions but never into
proofs. Mathlib and Lean are trusted and not followed.

    lake exe checkClosure Mod₁ Mod₂ … -- name₁ name₂ …

imports the modules, and prints as JSON, for each name, whether it resolves, its module, its
docstring, its closure and the axioms it rests on, together with the text and the term of every
declaration in a closure. The axioms are collected through proofs as well as statements, so that a
`sorry` or an unproved assumption anywhere beneath a declaration shows.

The term of a declaration is what a check is hashed over: a serialization of its elaborated type,
followed for a definition by its elaborated value, with every proof inside them replaced by a
placeholder (`eraseProofs`). Since it is the term and not its printing, a change that the
pretty-printer would hide still changes it, while the names of bound variables and binder
annotations, which do not change what a statement says, do not. The closure is followed through
the erased terms, so a declaration used only in a proof is not in it. The text of a declaration is
its pretty-printed type and value, with full names, for people to read.
-/

open Lean Meta

/-- The libraries whose declarations a closure follows, and the fixture of `checks.py selftest`. -/
def projectRoots : List Name := [`Linglib, `Studies, `Eval, `Lab, `ChecksFixture]

def moduleOf? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

def isProject (env : Environment) (n : Name) : Bool :=
  match moduleOf? env n with
  | some m => projectRoots.contains m.getRoot
  | none => false

def ppOptions : Options :=
  ({} : Options)
    |>.setBool `pp.fullNames true
    |>.setBool `pp.universes false
    |>.setBool `pp.proofs true
    |>.setBool `pp.funBinderTypes true
    |>.setBool `pp.deepTerms true
    |>.set `pp.maxSteps (1000000 : Nat)
    |>.set `format.width (100 : Nat)

def ppText (e : Expr) : MetaM String :=
  withOptions (fun _ ↦ ppOptions) do return toString (← ppExpr e)

/-- The placeholder that replaces a proof in a term. -/
def proofPlaceholder : Expr := .const `checks.proof []

/-- `e` with every proof in it replaced by `proofPlaceholder`. By proof irrelevance this does not
change what `e` means, and it makes a term independent of how its proofs were written. -/
def eraseProofs (e : Expr) : MetaM Expr :=
  transform e (pre := fun e ↦ do
    if ← (try isProof e catch _ => pure false) then return .done proofPlaceholder
    return .continue)

/-- A serialization of a closed term, in which each distinct subterm is a line naming its
children by line number. It records de Bruijn indices, constants with their universe levels, and
literals, and leaves out the names and annotations of binders, which `Expr.eqv` ignores too. -/
partial def serialize (e : Expr) : String := Id.run do
  let rec go (e : Expr) : StateM (Std.HashMap Expr Nat × Array String) Nat := do
    if let .mdata _ b := e then return ← go b
    if let some i := (← get).1.get? e then return i
    let line ← match e with
      | .bvar i => pure s!"bvar {i}"
      | .fvar _ | .mvar _ => pure "open"
      | .sort u => pure s!"sort {u}"
      | .const n us => pure s!"const {n} {us}"
      | .app f a => do pure s!"app {← go f} {← go a}"
      | .lam _ t b _ => do pure s!"lam {← go t} {← go b}"
      | .forallE _ t b _ => do pure s!"pi {← go t} {← go b}"
      | .letE _ t v b _ => do pure s!"let {← go t} {← go v} {← go b}"
      | .lit (.natVal n) => pure s!"nat {n}"
      | .lit (.strVal s) => pure s!"str {s.quote}"
      | .mdata .. => pure "mdata" -- unreachable: metadata is skipped above
      | .proj n i b => do pure s!"proj {n} {i} {← go b}"
    let (m, lines) ← get
    set (m.insert e lines.size, lines.push line)
    return lines.size
  let (_, _, lines) := (go e).run ({}, #[])
  return "\n".intercalate lines.toList

/-- The kind, text and term of a declaration, and the declarations its erased statement or body
mentions. -/
def describe (c : ConstantInfo) : MetaM (String × String × String × Array Name) := do
  let deps (es : List Expr) : Array Name :=
    es.foldl (fun acc e ↦ e.getUsedConstants.foldl (fun acc n ↦ acc.push n) acc) #[]
  let ty ← eraseProofs c.type
  match c with
  | .defnInfo d =>
    let val ← eraseProofs d.value
    return ("def", s!"{← ppText d.type}\n:=\n{← ppText d.value}",
      s!"{serialize ty}\n:=\n{serialize val}", deps [ty, val])
  | .thmInfo _ => return ("theorem", ← ppText c.type, serialize ty, deps [ty])
  | .opaqueInfo _ => return ("opaque", ← ppText c.type, serialize ty, deps [ty])
  | .axiomInfo _ => return ("axiom", ← ppText c.type, serialize ty, deps [ty])
  | .inductInfo i =>
    return ("inductive", s!"{← ppText c.type}\nconstructors: {i.ctors}",
      s!"{serialize ty}\nparams {i.numParams}\nconstructors {i.ctors}",
      (deps [ty]) ++ i.ctors.toArray)
  | .ctorInfo k => return ("constructor", ← ppText c.type, serialize ty, (deps [ty]).push k.induct)
  | .recInfo _ => return ("recursor", ← ppText c.type, serialize ty, deps [ty])
  | .quotInfo _ => return ("quot", ← ppText c.type, serialize ty, deps [ty])

structure Node where
  module : Name
  kind : String
  text : String
  term : String

structure ClosureState where
  nodes : Std.HashMap Name Node := {}
  /-- The direct project dependencies of each visited declaration. -/
  edges : Std.HashMap Name (Array Name) := {}

partial def visit (n : Name) : StateT ClosureState MetaM Unit := do
  if (← get).nodes.contains n then return
  let env ← getEnv
  let some c := env.find? n | return
  let (kind, text, term, deps) ← describe c
  let deps := deps.filter (isProject env) |>.toList.eraseDups.toArray
  modify fun s ↦ { s with
    nodes := s.nodes.insert n ⟨(moduleOf? env n).getD .anonymous, kind, text, term⟩
    edges := s.edges.insert n deps }
  for d in deps do visit d

/-- The declarations reachable from `n`, without `n` itself. -/
partial def reach (edges : Std.HashMap Name (Array Name)) (n : Name) : Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut todo := (edges.getD n #[]).toList
  while !todo.isEmpty do
    match todo with
    | [] => pure ()
    | m :: rest =>
      todo := rest
      if !seen.contains m && m != n then
        seen := seen.insert m
        todo := (edges.getD m #[]).toList ++ todo
  return seen.toArray.qsort (·.toString < ·.toString)

def run (names : List Name) : MetaM Json := do
  let env ← getEnv
  let mut roots : Array (String × Json) := #[]
  let mut st : ClosureState := {}
  for n in names do
    if env.contains n then
      (_, st) ← (visit n).run st
  for n in names do
    if env.contains n then
      let doc := (← findDocString? env n).getD ""
      let range ← findDeclarationRanges? n
      roots := roots.push (n.toString, Json.mkObj [
        ("found", true),
        ("module", toJson ((moduleOf? env n).getD .anonymous).toString),
        ("doc", doc),
        ("line", toJson (range.map (·.range.pos.line))),
        ("closure", toJson ((reach st.edges n).map Name.toString)),
        ("axioms", toJson ((← collectAxioms n).map Name.toString))])
    else
      roots := roots.push (n.toString, Json.mkObj [("found", false)])
  let nodes : Array (String × Json) := st.nodes.toArray.map fun (n, node) ↦
    (n.toString, Json.mkObj [
      ("module", node.module.toString), ("kind", node.kind), ("text", node.text),
      ("term", node.term)])
  return Json.mkObj [("roots", Json.mkObj roots.toList), ("nodes", Json.mkObj nodes.toList)]

def main (args : List String) : IO UInt32 := do
  let (mods, names) := args.span (· != "--")
  let names := names.drop 1
  initSearchPath (← findSysroot)
  let env ← importModules (mods.map fun m ↦ { module := m.toName }).toArray {}
    (trustLevel := 1024)
  let ctx : Core.Context := { fileName := "<checks>", fileMap := default, maxHeartbeats := 0 }
  let (json, _) ← ((run (names.map String.toName)).run' {} {}).toIO ctx { env }
  IO.println json.compress
  return 0
