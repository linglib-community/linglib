import Lean

/-!
# Duplicate definitions

Reports definitions of the library that are the same term once abbreviations, instance projections
and set-builder plumbing are unfolded, so that `Set α` reads as `α → Prop`. Two definitions with
equal normalized type and value are a duplicate pair; a definition whose value is another constant
is an alias. Hashing uses Lean's structural hash, which ignores binder names and respects sharing.

Two modules that declare the same name cannot be imported together. Such clashes are read off the
olean headers and reported first; the side with fewer dependents is then left out, with its
dependents, so that the rest of the library can be loaded and compared.

Run after `lake build`, informational only:

    lake env lean --run scripts/find_duplicates.lean [Module ...]

With no arguments it reads every module under `Linglib/` (except the generated `Data/` and the
lexical `Fragments/`) and `Studies/`.
-/

open Lean Meta

namespace FindDuplicates

/-- Set and relation plumbing, unfolded so that sets read as predicates. -/
def plumbing : NameSet := [`Set, `setOf, `Set.ofPred, `Set.Mem, `Set.Subset, `Set.Nonempty,
  `Set.inter, `Set.union, `Set.compl, `Set.univ, `Set.diff, `Set.image, `Set.preimage, `SetRel,
  `Function.comp, `id, `Set.singleton, `Set.insert].foldl NameSet.insert {}

/-- Unfold reducible constants, the plumbing, and class projections applied to instances, with
beta and eta; `none` past the step budget. -/
def normalize (e : Expr) (budget : Nat := 4000) : MetaM (Option Expr) := do
  let steps ← IO.mkRef 0
  try
    let e ← Meta.transform e (pre := fun e => do
      let e := e.headBeta
      steps.modify (· + 1)
      if (← steps.get) > budget then throwError "budget"
      let .const n _ := e.getAppFn | return .continue
      if let some e' ← withTransparency .instances <| unfoldProjInst? e then
        return .visit e'.headBeta
      if plumbing.contains n || (← isReducible n) then
        if let some e' ← unfoldDefinition? e (ignoreTransparency := true) then
          return .visit e'.headBeta
      return .continue)
    return some e.eta
  catch _ => return none

/-- Erase universe levels, keeping `Prop` apart from `Type`. -/
def eraseLevels (e : Expr) : Expr :=
  e.replace fun
    | .const n _ => some (.const n [])
    | .sort u => some (.sort (if u.isZero then Level.zero else Level.one))
    | _ => none

def skip (env : Environment) (n : Name) : Bool :=
  n.isInternalDetail || isAuxRecursor env n || isNoConfusion env n ||
    (env.getProjectionFnInfo? n).isSome || isInstanceCore env n || isInstanceCore env n.getPrefix ||
    (n.toString.splitOn ".match_").length > 1 || (n.toString.splitOn ".proof_").length > 1

structure Row where
  name : Name
  module : Name
  depth : Nat
  typeFormer : Bool
  aliasOf : Option Name

/-- Fingerprint every definition of `mods`. -/
def collect (mods : Array Name) : MetaM (Std.HashMap (UInt64 × UInt64) (Array Row) × Nat) := do
  let env ← getEnv
  let mut groups : Std.HashMap (UInt64 × UInt64) (Array Row) := {}
  let mut failed := 0
  for m in mods do
    let some idx := env.getModuleIdx? m | continue
    for n in env.header.moduleData[idx.toNat]!.constNames do
      if skip env n then continue
      let some (.defnInfo d) := env.find? n | continue
      let r ← try withCurrHeartbeats do
          let some t ← normalize d.type | return none
          let some v ← normalize d.value | return none
          let typeFormer ← forallTelescope d.type fun _ b => pure (b.isSort && !b.isProp)
          let aliasOf := match v.eta with | .const c _ => some c | _ => none
          pure (some ((eraseLevels t).hash, (eraseLevels v).hash,
            { name := n, module := m, depth := v.approxDepth.toNat, typeFormer, aliasOf : Row }))
        catch _ => pure none
      match r with
      | some (ht, hv, row) => groups := groups.insert (ht, hv) ((groups.getD (ht, hv) #[]).push row)
      | none => failed := failed + 1
  return (groups, failed)

/-- The modules under `Linglib/` (without `Data/` and `Fragments/`) and `Studies/`. -/
def discover : IO (Array Name) := do
  let mut mods := #[]
  for root in ["Linglib", "Studies"] do
    for p in ← System.FilePath.walkDir root do
      let s := p.toString
      if p.extension != some "lean" || s.startsWith "Linglib/Data/" ||
          s.startsWith "Linglib/Fragments/" then continue
      mods := mods.push (((s.splitOn ".lean").headD s).replace "/" ".").toName
  return mods.qsort (·.toString < ·.toString)

/-- The library modules reachable from `mods`, with their imports and declared names, read from
the olean headers. -/
partial def readGraph (mods : Array Name) : IO (Std.HashMap Name (Array Name × Array Name)) := do
  let g ← IO.mkRef ({} : Std.HashMap Name (Array Name × Array Name))
  let rec visit (m : Name) : IO Unit := do
    if (← g.get).contains m then return
    unless m.getRoot == `Linglib || m.getRoot == `Studies do return
    let (d, _) ← readModuleData (← findOLean m)
    let imps := d.imports.map (·.module)
    g.modify (·.insert m (imps, d.constNames))
    for i in imps do visit i
  for m in mods do visit m
  g.get

/-- Names Lean generates on demand in each module that needs them, such as equation and congruence
lemmas; the same such name in two modules is no clash. -/
def generated (n : Name) : Bool :=
  n.isInternalDetail || match n with
    | .str _ s => s == "congr_simp" || s == "eq_def" || s == "eq_unfold" || s == "sizeOf_spec" ||
        (s.startsWith "eq_" && (s.drop 3).all Char.isDigit)
    | _ => false

/-- The modules that import any of `ms`, transitively, together with `ms`. -/
def dependents (graph : Std.HashMap Name (Array Name × Array Name)) (ms : Array Name) : NameSet :=
  let rev : Std.HashMap Name (Array Name) := graph.fold (init := {}) fun acc m (imps, _) =>
    imps.foldl (fun acc i => acc.insert i ((acc.getD i #[]).push m)) acc
  Id.run do
    let mut seen : NameSet := {}
    let mut todo := ms.toList
    for _ in [0:graph.size + ms.size] do
      match todo with
      | [] => break
      | m :: rest =>
        todo := rest
        if seen.contains m then continue
        seen := seen.insert m
        todo := (rev.getD m #[]).toList ++ todo
    return seen

def line (g : Array Row) : String :=
  " == ".intercalate (g.toList.map fun r => s!"{r.name} ({r.module})")

end FindDuplicates

open FindDuplicates in
unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mods ← if args.isEmpty then discover else pure (args.map String.toName).toArray
  let graph ← readGraph mods
  let owners : Std.HashMap Name (Array Name) := graph.fold (init := {}) fun acc m (_, cs) =>
    cs.foldl (fun acc c => acc.insert c ((acc.getD c #[]).push m)) acc
  let mut pairs : Std.HashMap (Name × Name) (Array Name) := {}
  for (c, ms) in owners do
    if ms.size > 1 && !generated c then
      let ms := ms.qsort (·.toString < ·.toString)
      pairs := pairs.insert (ms[0]!, ms[1]!) ((pairs.getD (ms[0]!, ms[1]!) #[]).push c)
  IO.println s!"# Names declared in two modules ({pairs.size} module pairs)"
  let mut dropped := #[]
  for ((a, b), cs) in pairs do
    let shown := cs.filter (!·.isInternalDetail) |>.qsort (·.toString < ·.toString)
    IO.println s!"{a} and {b}: {", ".intercalate (shown.toList.take 5 |>.map toString)}"
    let da := (dependents graph #[a]).size
    let db := (dependents graph #[b]).size
    dropped := dropped.push (if da ≤ db then a else b)
  let excluded := dependents graph dropped
  let mods := mods.filter (!excluded.contains ·)
  IO.println s!"left out to load the rest: {excluded.size} modules\n"
  let imports := mods.map fun m => ({ module := m } : Import)
  let env ← importModules imports {} (trustLevel := 1024) (loadExts := true)
  let ctx : Core.Context :=
    { fileName := "find_duplicates", fileMap := default, maxHeartbeats := 50000000 }
  let ((groups, failed), _) ← ((collect mods).run' {} {}).toIO ctx { env }
  let multi := groups.toArray.filter fun (_, g) => (g.map (·.module)).toList.eraseDups.length > 1
  let (types, terms) := (multi.map (·.2)).partition (·.any (·.typeFormer))
  let terms := terms.filter (·.any (·.depth ≥ 4))
  let aliases := groups.toArray.flatMap fun (_, g) =>
    g.filter fun r => r.aliasOf.isSome && !r.typeFormer
  IO.println s!"# Duplicate definitions across modules ({terms.size} groups)"
  for g in terms.qsort (fun a b => a.size > b.size) do IO.println (line g)
  IO.println s!"\n# Type synonyms across modules ({types.size} groups)"
  for g in types do IO.println (line g)
  IO.println s!"\n# Aliases ({aliases.size})"
  for r in aliases do IO.println s!"{r.name} ({r.module}) := {r.aliasOf.get!}"
  let defs := groups.fold (fun n _ g => n + g.size) 0
  IO.println s!"\n{mods.size} modules, {defs} definitions, {failed} not normalized"
  return 0
