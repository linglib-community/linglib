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
docstring and its closure, together with the text of every declaration in a closure. The text of a
declaration is its pretty-printed type, followed for a definition by its pretty-printed value, with
full names, so that it does not depend on the namespaces open where it was written.
-/

open Lean Meta

/-- The libraries whose declarations a closure follows. -/
def projectRoots : List Name := [`Linglib, `Studies, `Eval, `Lab]

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
    |>.setBool `pp.deepTerms true
    |>.set `pp.maxSteps (1000000 : Nat)
    |>.set `format.width (100 : Nat)

def ppText (e : Expr) : MetaM String :=
  withOptions (fun _ ↦ ppOptions) do return toString (← ppExpr e)

/-- The text of a declaration and the declarations its statement or body mentions. -/
def describe (c : ConstantInfo) : MetaM (String × String × Array Name) := do
  let deps (es : List Expr) : Array Name :=
    es.foldl (fun acc e ↦ e.getUsedConstants.foldl (fun acc n ↦ acc.push n) acc) #[]
  match c with
  | .defnInfo d =>
    return ("def", s!"{← ppText d.type}\n:=\n{← ppText d.value}", deps [d.type, d.value])
  | .thmInfo t => return ("theorem", ← ppText t.type, deps [t.type])
  | .opaqueInfo o => return ("opaque", ← ppText o.type, deps [o.type])
  | .axiomInfo a => return ("axiom", ← ppText a.type, deps [a.type])
  | .inductInfo i =>
    return ("inductive", s!"{← ppText i.type}\nconstructors: {i.ctors}",
      (deps [i.type]) ++ i.ctors.toArray)
  | .ctorInfo k => return ("constructor", ← ppText k.type, (deps [k.type]).push k.induct)
  | .recInfo r => return ("recursor", ← ppText r.type, deps [r.type])
  | .quotInfo q => return ("quot", ← ppText q.type, deps [q.type])

structure Node where
  module : Name
  kind : String
  text : String

structure ClosureState where
  nodes : Std.HashMap Name Node := {}
  /-- The direct project dependencies of each visited declaration. -/
  edges : Std.HashMap Name (Array Name) := {}

partial def visit (n : Name) : StateT ClosureState MetaM Unit := do
  if (← get).nodes.contains n then return
  let env ← getEnv
  let some c := env.find? n | return
  let (kind, text, deps) ← describe c
  let deps := deps.filter (isProject env) |>.toList.eraseDups.toArray
  modify fun s ↦ { s with
    nodes := s.nodes.insert n ⟨(moduleOf? env n).getD .anonymous, kind, text⟩
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
        ("closure", toJson ((reach st.edges n).map Name.toString))])
    else
      roots := roots.push (n.toString, Json.mkObj [("found", false)])
  let nodes : Array (String × Json) := st.nodes.toArray.map fun (n, node) ↦
    (n.toString, Json.mkObj [
      ("module", node.module.toString), ("kind", node.kind), ("text", node.text)])
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
