/-
Declaration-level dependencies of the library, for `scripts/gen_tendrils.py`.

`lean --run scripts/tendrils/Extract.lean <modules.txt> <out.tsv>` loads every listed module with its
private data and writes one line per declaration: name, module, kind, flags, the declarations its type
mentions, the declarations its value mentions, those reached only through a default argument, and the
areas of Lean and mathlib it rests on.
-/
import Lean
open Lean

/-- Replace `optParam α d` by `α`, so that a default value is not counted as a dependency. -/
def stripOpt (e : Expr) : Expr :=
  e.replace fun e => if e.isAppOfArity ``optParam 2 then some (e.getArg! 0) else none

def hasBigLit (e : Expr) : Bool :=
  (e.find? fun | .lit (.natVal n) => n ≥ 1000 | _ => false).isSome

def isLing (m : Name) : Bool := m.getRoot == `Linglib || m.getRoot == `Studies

def area (m : Name) : String :=
  match m.components with
  | a :: b :: _ => if a == `Mathlib then s!"{a}.{b}" else toString a
  | [a] => toString a
  | [] => "?"

unsafe def main (args : List String) : IO Unit := do
  let mods := ((← IO.FS.lines args[0]!).filter (· ≠ "")).map String.toName
  let sp ← addSearchPathFromEnv {}
  initSearchPath (← findSysroot) sp
  let imports := mods.map fun m => ({ module := m, importAll := true } : Import)
  let env ← importModules imports {} (loadExts := false)
  let modNames := env.header.moduleNames
  -- pass 1: ids for linglib constants
  let mut ids : Std.HashMap Name Nat := {}
  let mut names : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if let some i := env.getModuleIdxFor? n then
      if isLing modNames[i.toNat]! then
        ids := ids.insert n names.size
        names := names.push n
  let h ← IO.FS.Handle.mk args[1]! .write
  let split (s : NameSet) : Array Nat × Array String × Bool × Nat := Id.run do
    let mut a : Array Nat := #[]
    let mut ext : Std.HashSet String := {}
    let mut sry := false
    let mut nx := 0
    for c in s do
      if c == ``sorryAx then sry := true
      match ids[c]? with
      | some i => a := a.push i
      | none =>
        nx := nx + 1
        if let some i := env.getModuleIdxFor? c then ext := ext.insert (area modNames[i.toNat]!)
    return (a, ext.toArray, sry, nx)
  let join {α} [ToString α] (a : Array α) : String := ",".intercalate (a.toList.map toString)
  for n in names do
    let some ci := env.find? n | continue
    let m := modNames[(env.getModuleIdxFor? n).get!.toNat]!
    let ty := ci.type
    let tyS := (stripOpt ty).getUsedConstantsAsSet
    let tyAll := ty.getUsedConstantsAsSet
    let dflt := tyAll.foldl (fun (acc : NameSet) c => if tyS.contains c then acc else acc.insert c) {}
    let (kind, valS, big) : String × NameSet × Bool :=
      match ci with
      | .thmInfo v => ("thm", v.value.getUsedConstantsAsSet, false)
      | .defnInfo v => ("def", (stripOpt v.value).getUsedConstantsAsSet, hasBigLit v.value)
      | .opaqueInfo v => ("opaque", v.value.getUsedConstantsAsSet, false)
      | .axiomInfo _ => ("axiom", {}, false)
      | .inductInfo v => ("ind", v.ctors.foldl (fun (s : NameSet) c => s.insert c) {}, false)
      | .ctorInfo v => ("ctor", (NameSet.empty.insert v.induct), false)
      | .recInfo _ => ("rec", {}, false)
      | .quotInfo _ => ("quot", {}, false)
    let (t, te, _, nt) := split tyS
    let (v, ve, sry, nv) := split valS
    let (d, _, _, _) := split dflt
    let fl := (if n.isInternalDetail then "i" else "") ++ (if isPrivateName n then "p" else "") ++
      (if big then "b" else "") ++ (if sry then "s" else "")
    let shown := (privateToUserName? n).getD n
    h.putStrLn s!"{shown}\t{m}\t{kind}\t{fl}\t{join t}\t{join v}\t{join d}\t{join te}\t{join ve}\t{nt}\t{nv}"
  h.flush
  IO.println s!"{names.size} constants from {mods.size} modules"
