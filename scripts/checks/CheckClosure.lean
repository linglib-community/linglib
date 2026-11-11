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

    lake exe checkClosure [--renames FILE] Mod₁ Mod₂ … -- name₁ name₂ …

imports the modules, and prints as JSON, for each name, whether it resolves, its module, its
docstring, its closure and the axioms it rests on, together with the text and the term of every
declaration in a closure, and the renamed constants among those the closures mention (`aliases`,
below). The axioms are collected through proofs as well as statements, so that a
`sorry` or an unproved assumption anywhere beneath a declaration shows.

The term of a declaration is what a check is hashed over: a serialization of its elaborated type,
followed for a definition by its elaborated value, with every proof inside them replaced by a
placeholder (`eraseProofs`). Since it is the term and not its printing, a change that the
pretty-printer would hide still changes it, while the names of bound variables and binder
annotations, which do not change what a statement says, do not. The closure is followed through
the erased terms, so a declaration used only in a proof is not in it. The text of a declaration is
its pretty-printed type and value, with full names, for people to read.

A Lean or Mathlib upgrade often renames a constant, keeping the old name for a while as a
deprecated alias of the new one. So that such a rename does not change a term, every name of a
recorded rename (`checks/renames.toml`) is replaced in a term by a single one of them, as the JSON
object that `--renames` names maps them (`canonicalize`). A rename is recorded only if the old name
is an alias of the new one (`renameOf?`), so the replacement does not change what a term says.
`aliases` lists every such rename of a constant that the closures mention under either name, so
that `checks.py` can record it before the alias is removed.
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
    |>.setBool `pp.fieldNotation.generalized false
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

/-- `e` with every constant that `renames` maps replaced by its image. -/
def canonicalize (renames : NameMap Name) (e : Expr) : Expr :=
  if renames.isEmpty then e else
    e.replace fun
      | .const n us => (renames.find? n).map (.const · us)
      | _ => none

/-- The new name of `old`, if `old` is a Lean or Mathlib constant deprecated in favour of a
constant of which it is an alias: a definition whose value is that constant, up to eta, at the
same universe levels and with the same type. A deprecation may point to a constant that means
something else, and is then not a rename. -/
def renameOf? (env : Environment) (old : Name) : Option Name := do
  let new ← (← Linter.deprecatedAttr.getParam? env old).newName?
  guard (!isProject env old && !isProject env new)
  let .defnInfo d ← env.find? old | none
  let c ← env.find? new
  guard (c.levelParams.length == d.levelParams.length)
  let us := d.levelParams.map Level.param
  guard (d.value.eta == .const new us)
  guard (c.type.instantiateLevelParams c.levelParams us == d.type)
  return new

/-- The kind, text and term of a declaration, the latter with `renames` applied, and the
declarations its erased statement or body mentions. Since a rename is of Lean and Mathlib
constants, it makes no difference to the project declarations mentioned. -/
def describe (renames : NameMap Name) (c : ConstantInfo) :
    MetaM (String × String × String × Array Name) := do
  let deps (es : List Expr) : Array Name :=
    es.foldl (fun acc e ↦ e.getUsedConstants.foldl (fun acc n ↦ acc.push n) acc) #[]
  let ser (e : Expr) : String := serialize (canonicalize renames e)
  let ty ← eraseProofs c.type
  match c with
  | .defnInfo d =>
    let val ← eraseProofs d.value
    return ("def", s!"{← ppText d.type}\n:=\n{← ppText d.value}",
      s!"{ser ty}\n:=\n{ser val}", deps [ty, val])
  | .thmInfo _ => return ("theorem", ← ppText c.type, ser ty, deps [ty])
  | .opaqueInfo _ => return ("opaque", ← ppText c.type, ser ty, deps [ty])
  | .axiomInfo _ => return ("axiom", ← ppText c.type, ser ty, deps [ty])
  | .inductInfo i =>
    return ("inductive", s!"{← ppText c.type}\nconstructors: {i.ctors}",
      s!"{ser ty}\nparams {i.numParams}\nconstructors {i.ctors}",
      (deps [ty]) ++ i.ctors.toArray)
  | .ctorInfo k => return ("constructor", ← ppText c.type, ser ty, (deps [ty]).push k.induct)
  | .recInfo _ => return ("recursor", ← ppText c.type, ser ty, deps [ty])
  | .quotInfo _ => return ("quot", ← ppText c.type, ser ty, deps [ty])

structure Node where
  module : Name
  kind : String
  text : String
  term : String

structure ClosureState where
  nodes : Std.HashMap Name Node := {}
  /-- The direct project dependencies of each visited declaration. -/
  edges : Std.HashMap Name (Array Name) := {}
  /-- The Lean and Mathlib constants that the visited declarations mention. -/
  mentioned : NameSet := {}

partial def visit (renames : NameMap Name) (n : Name) : StateT ClosureState MetaM Unit := do
  if (← get).nodes.contains n then return
  let env ← getEnv
  let some c := env.find? n | return
  let (kind, text, term, used) ← describe renames c
  let deps := used.filter (isProject env) |>.toList.eraseDups.toArray
  modify fun s ↦ { s with
    nodes := s.nodes.insert n ⟨(moduleOf? env n).getD .anonymous, kind, text, term⟩
    edges := s.edges.insert n deps
    mentioned := used.foldl (fun acc m ↦ if isProject env m then acc else acc.insert m)
      s.mentioned }
  for d in deps do visit renames d

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

/-- The renames (`renameOf?`) in which a constant of `mentioned` is the old name or the new one,
with the date of each deprecation. -/
def aliases (env : Environment) (mentioned : NameSet) : Array Json := Id.run do
  let mut out := #[]
  for (old, _) in env.constants.toList do
    if let some new := renameOf? env old then
      if mentioned.contains old || mentioned.contains new then
        let since := (Linter.deprecatedAttr.getParam? env old).bind (·.since?)
        out := out.push (Json.mkObj [("old", old.toString), ("new", new.toString),
          ("since", toJson since)])
  return out.qsort (·.compress < ·.compress)

/-! ### Content hashes

A content hash names a project declaration by what it says instead of by what it is called: the
hash of its erased term, in which every project constant is replaced by that constant's own
content hash. Renaming or moving a definition or a theorem, or one it uses, then changes no hash.
The primitives keep their names, since nothing else says what they stand for: an inductive type
is hashed with its mutual block under its own name and those of its constructors and fields, and
an axiom or an opaque constant under its name. -/

structure ContentState where
  hashes : Std.HashMap Name String := {}
  inProgress : NameSet := {}

abbrev ContentM := StateT ContentState MetaM

def digest (s : String) : String :=
  String.ofList (Nat.toDigits 16 (hash s).toNat ++ Nat.toDigits 16 (hash (s ++ "\x00salt")).toNat)

/-- `serialize`, with project constants and structure names read through `ref`. -/
partial def serializeBy (ref : Name → Option String) (e : Expr) : String := Id.run do
  let rec go (e : Expr) : StateM (Std.HashMap Expr Nat × Array String) Nat := do
    if let .mdata _ b := e then return ← go b
    if let some i := (← get).1.get? e then return i
    let line ← match e with
      | .bvar i => pure s!"bvar {i}"
      | .fvar _ | .mvar _ => pure "open"
      | .sort u => pure s!"sort {u}"
      | .const n us => pure (match ref n with
          | some h => s!"ref {h} {us}"
          | none => s!"const {n} {us}")
      | .app f a => do pure s!"app {← go f} {← go a}"
      | .lam _ t b _ => do pure s!"lam {← go t} {← go b}"
      | .forallE _ t b _ => do pure s!"pi {← go t} {← go b}"
      | .letE _ t v b _ => do pure s!"let {← go t} {← go v} {← go b}"
      | .lit (.natVal n) => pure s!"nat {n}"
      | .lit (.strVal s) => pure s!"str {s.quote}"
      | .mdata .. => pure "mdata"
      | .proj n i b => do pure s!"proj {(ref n).getD n.toString} {i} {← go b}"
    let (m, lines) ← get
    set (m.insert e lines.size, lines.push line)
    return lines.size
  let (_, _, lines) := (go e).run ({}, #[])
  return "\n".intercalate lines.toList

/-- The term with its universe parameters named by position. -/
def positional (c : ConstantInfo) (e : Expr) : Expr :=
  e.instantiateLevelParams c.levelParams
    ((List.range c.levelParams.length).map fun i ↦ .param (.mkNum `u i))

/-- The structures an erased term projects from. -/
partial def projStructs (e : Expr) : NameSet := Id.run do
  let rec go (e : Expr) : StateM (Std.HashSet Expr × NameSet) Unit := do
    if (← get).1.contains e then return
    modify fun (seen, acc) ↦ (seen.insert e, acc)
    match e with
    | .proj n _ b => modify (fun (seen, acc) ↦ (seen, acc.insert n)); go b
    | .app f a => go f; go a
    | .lam _ t b _ | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b => go b
    | _ => pure ()
  let ((), _, acc) := (go e).run ({}, {})
  return acc

/-- The project constants an erased term mentions, including the structures it projects from. -/
def projectConstants (env : Environment) (e : Expr) : Array Name :=
  (e.getUsedConstants ++ (projStructs e).toArray).filter (isProject env)

mutual

/-- The serialization of an erased term, its project constants read as content hashes, except
those in `self`, the block being hashed. -/
partial def contentTerm (renames : NameMap Name) (self : NameMap String) (c : ConstantInfo)
    (e : Expr) : ContentM String := do
  let env ← getEnv
  let e := positional c (canonicalize renames (← eraseProofs e))
  let mut refs : NameMap String := self
  for n in projectConstants env e do
    unless refs.contains n do
      refs := refs.insert n (← contentHash renames n)
  return serializeBy refs.find? e

partial def contentHash (renames : NameMap Name) (n : Name) : ContentM String := do
  if let some h := (← get).hashes.get? n then return h
  if (← get).inProgress.contains n then return s!"cycle {n}"
  let env ← getEnv
  let some c := env.find? n | return s!"unknown {n}"
  modify fun s ↦ { s with inProgress := s.inProgress.insert n }
  let h ← match c with
    | .inductInfo i => do
      let mut self : NameMap String := {}
      let mut k := 0
      for ind in i.all do
        self := self.insert ind s!"self.{k}"
        if let some (.inductInfo j) := env.find? ind then
          let mut m := 0
          for ctor in j.ctors do
            self := self.insert ctor s!"self.{k}.c{m}"
            m := m + 1
        k := k + 1
      let mut text := ""
      for ind in i.all do
        if let some ci@(.inductInfo j) := env.find? ind then
          let fields := if isStructure env ind then getStructureFields env ind else #[]
          text := text ++ s!"\nind {ind} {j.numParams} {j.numIndices} {fields}\n{← contentTerm renames self ci ci.type}"
          for ctor in j.ctors do
            if let some cc := env.find? ctor then
              text := text ++ s!"\nctor {ctor}\n{← contentTerm renames self cc cc.type}"
      let g := digest text
      for (name, tag) in self.toList do
        modify fun s ↦ { s with hashes := s.hashes.insert name s!"{g}.{tag}" }
      for ind in i.all do
        modify fun s ↦ { s with hashes := s.hashes.insert (ind ++ `rec) s!"{g}.{(self.find? ind).getD ""}.rec" }
      pure s!"{g}.{(self.find? n).getD ""}"
    | .ctorInfo k => do
      discard <| contentHash renames k.induct
      pure (((← get).hashes.get? n).getD s!"ctor {n}")
    | .recInfo r => do
      discard <| contentHash renames r.all.head!
      pure (((← get).hashes.get? n).getD s!"rec {n}")
    | .defnInfo d => do
      pure (digest s!"def\n{← contentTerm renames {} c d.type}\n:=\n{← contentTerm renames {} c d.value}")
    | .thmInfo _ => do pure (digest s!"thm\n{← contentTerm renames {} c c.type}")
    | _ => do pure (digest s!"nominal {n}\n{← contentTerm renames {} c c.type}")
  modify fun s ↦ { s with hashes := s.hashes.insert n h, inProgress := s.inProgress.erase n }
  return h

end

def run (renames : NameMap Name) (names : List Name) (all : Bool) : MetaM Json := do
  let env ← getEnv
  let mut roots : Array (String × Json) := #[]
  let mut st : ClosureState := {}
  let mut cs : ContentState := {}
  for n in names do
    if env.contains n then
      (_, st) ← (visit renames n).run st
  for n in names do
    if env.contains n then
      let doc := (← findDocString? env n).getD ""
      let (content, cs') ← (contentHash renames n).run cs
      cs := cs'
      let range ← findDeclarationRanges? n
      roots := roots.push (n.toString, Json.mkObj [
        ("found", true),
        ("module", toJson ((moduleOf? env n).getD .anonymous).toString),
        ("doc", doc),
        ("content", content),
        ("line", toJson (range.map (·.range.pos.line))),
        ("closure", toJson ((reach st.edges n).map Name.toString)),
        ("axioms", toJson ((← collectAxioms n).map Name.toString))])
    else
      roots := roots.push (n.toString, Json.mkObj [("found", false)])
  let nodes : Array (String × Json) := st.nodes.toArray.map fun (n, node) ↦
    (n.toString, Json.mkObj [
      ("module", node.module.toString), ("kind", node.kind), ("text", node.text),
      ("term", node.term)])
  let mut every : Array (String × Json) := #[]
  if all then
    for (n, c) in env.constants.toList do
      if isProject env n && !n.isInternal && !(c matches .recInfo _) then
        let (h, cs') ← (contentHash renames n).run cs
        cs := cs'
        every := every.push (h, n.toString)
  return Json.mkObj [("roots", Json.mkObj roots.toList), ("nodes", Json.mkObj nodes.toList),
    ("aliases", toJson (aliases env st.mentioned)), ("all", Json.mkObj every.toList)]

/-- The map from names to names in the JSON object of the file at `path`. -/
def readRenames (path : String) : IO (NameMap Name) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let obj ← IO.ofExcept json.getObj?
  obj.foldlM (init := {}) fun acc k v ↦ do
    let v ← IO.ofExcept v.getStr?
    return acc.insert k.toName v.toName

def main (args : List String) : IO UInt32 := do
  let ((renames : NameMap Name), args) ← match args with
    | "--renames" :: path :: rest => do pure (← readRenames path, rest)
    | _ => pure ({}, args)
  let (all, args) := match args with
    | "--all" :: rest => (true, rest)
    | _ => (false, args)
  let (mods, names) := args.span (· != "--")
  let names := names.drop 1
  initSearchPath (← findSysroot)
  let env ← importModules (mods.map fun m ↦ { module := m.toName }).toArray {}
    (trustLevel := 1024)
  let ctx : Core.Context := { fileName := "<checks>", fileMap := default, maxHeartbeats := 0 }
  let (json, _) ← ((run renames (names.map String.toName) all).run' {} {}).toIO ctx { env }
  IO.println json.compress
  return 0
