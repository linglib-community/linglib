import Lean

/-!
# Export the verdicts of `Eval` and `Lab`

Writes every verdict that `Eval` and `Lab` prove as JSON, for `scripts/gen_eval_page.py`, which runs
this file after a line importing every module of the two libraries. The export reads the theorems
whose statements are equations about an `Eval.Experiment`: a verdict `X.verdict T c = v`, an
observation `X.observed c = o`, the stipulations of a parser `π.stipulations = {…}`, or two parsers
that parse alike. A theorem whose variables range over finite enumerations, such as the accounts or
the cells of a design, is instantiated at each of their values, and each right-hand side is reduced
to a constructor by Lean. So the page shows what the theorems say and nothing typed by hand, and a
new experiment reaches the page through its theorems alone. A theorem that rests on `sorry` stops
the export.

It also writes, for each theory scored, the definitions of `Linglib` and `Studies` its registration
reaches once the declarations of `Eval` and `Lab` are unfolded (`definitions`).

The output path is `$EVAL_PAGE_JSON`, by default `.lake/build/eval-page/verdicts.json`.
-/

open Lean Meta

namespace EvalPage

/-- The libraries whose theorems are read. -/
def libraries : List String := ["Eval", "Lab"]

/-- The library a declaration belongs to, which is the root of its module. -/
def libraryOf (n : Name) : CoreM Name := do
  let env ← getEnv
  return match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!.getRoot
    | none => .anonymous

/-- The definitions of `Linglib` and `Studies` a term reaches once the declarations of `Eval` and
`Lab` in it are unfolded, in the order they occur; `none` if a case split is left stuck, since it
would reach every case. Instances, theorems, types and constructors are left out. -/
def reaches (e : Expr) : MetaM (Option (List Name)) := do
  let scoring (_ : Meta.Config) (info : ConstantInfo) : CoreM Bool :=
    return libraries.contains (← libraryOf info.name).toString
  let r ← withCanUnfoldPred scoring <| reduce e (skipTypes := false)
  let env ← getEnv
  let cs := r.getUsedConstants
  if cs.any fun c ↦ isMatcherCore env c || isCasesOnRecursor env c then return none
  let mut out := #[]
  for c in cs do
    unless [`Linglib, `Studies].contains (← libraryOf c) do continue
    let some (.defnInfo _) := env.find? c | continue
    if c.isInternal || (← isInstance c) || out.contains c then continue
    out := out.push c
  return some out.toList

/-- The definitions of `Eval` and `Lab` with an explicit argument in the enumeration `A`, each as
a function of that argument. -/
def takers (A : Name) : MetaM (List Expr) := do
  let env ← getEnv
  let mut out := #[]
  for (n, info) in env.constants.map₁.toList do
    let .defnInfo d := info | continue
    if n.isInternal || !libraries.contains (← libraryOf n).toString || (← isInstance n) then
      continue
    let f? ← forallTelescope d.type fun xs _ ↦ do
      for h : i in [:xs.size] do
        let x := xs[i]
        unless (← x.fvarId!.getBinderInfo).isExplicit do continue
        unless (← whnfR (← inferType x)).isConstOf A do continue
        let rest := xs.eraseIdx! i
        let body := mkAppN (mkConst n (d.levelParams.map mkLevelParam)) xs
        return some (n, ← mkLambdaFVars #[x] (← mkLambdaFVars rest body))
      return none
    if let some f := f? then out := out.push f
  return (out.qsort (·.1.toString < ·.1.toString)).toList.map (·.2)

/-- The definitions each theory rests on, which are those its term reaches. A theory that is a bare
constructor of an enumeration reaches nothing itself, so for it they are those each definition
taking the enumeration reaches at that constructor, less those every constructor reaches. -/
def definitions (theories : List (Name × Expr)) : MetaM (List (Name × List Name)) := do
  let env ← getEnv
  let mut cache : Std.HashMap Name (List Expr) := {}
  let mut out := []
  for (T, t) in theories do
    let mut found := (← reaches t).getD []
    if let (true, some (.ctorInfo ci)) := (found.isEmpty, env.find? T) then
      let fs ← match cache[ci.induct]? with
        | some fs => pure fs
        | none => takers ci.induct
      cache := cache.insert ci.induct fs
      let at_ (c : Name) : MetaM (List Name) :=
        fs.foldlM (fun ns f ↦ return ns ++ ((← reaches (f.beta #[mkConst c])).getD [])) []
      let mine ← at_ T
      let .inductInfo ii ← getConstInfo ci.induct | unreachable!
      let mut shared := if ii.ctors.length > 1 then mine else []
      for c in ii.ctors do
        if shared.isEmpty then break
        let theirs ← at_ c
        shared := shared.filter theirs.contains
      found := mine.filter (!shared.contains ·)
    out := out ++ [(T, found.eraseDups)]
  return out

/-- The constructors of an enumeration, or `none` for any other type. -/
def enumCtors (ty : Expr) : MetaM (Option (List Name)) := do
  let .const n _ := (← whnfR ty).getAppFn | return none
  let some (.inductInfo info) := (← getEnv).find? n | return none
  if info.numParams ≠ 0 ∨ info.numIndices ≠ 0 then return none
  for c in info.ctors do
    let .ctorInfo ci ← getConstInfo c | return none
    if ci.numFields ≠ 0 then return none
  return some info.ctors

/-- The position of a constructor in its type, used to order rows and columns. -/
def rank (n : Name) : MetaM Nat := do
  match (← getEnv).find? n with
  | some (.ctorInfo ci) => return ci.cidx
  | _ => return 1000

/-- A closed term reduced to its tree of constructors. -/
partial def ctorTree (e : Expr) : MetaM Json := do
  let e ← whnf e
  if let .lit (.natVal n) := e then return toJson n
  let .const c _ := e.getAppFn | throwError "does not reduce to a constructor: {e}"
  let .ctorInfo info ← getConstInfo c | throwError "does not reduce to a constructor: {e}"
  let fields := e.getAppArgs.extract info.numParams e.getAppNumArgs
  if fields.isEmpty then return toJson c.getString!
  return Json.mkObj [("ctor", toJson c.getString!), ("args", toJson (← fields.mapM ctorTree))]

/-- The elements of a finite set written as a literal, `∅`, `{a}` or `{a, b, …}`. -/
partial def literalElems (e : Expr) : MetaM (List Expr) := do
  let e := e.consumeMData
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``EmptyCollection.emptyCollection, _ => return []
  | some ``Singleton.singleton, args => return [args[3]!]
  | some ``Insert.insert, args => return args[3]! :: (← literalElems args[4]!)
  | _, _ => throwError "not a finite set literal: {e}"

/-- A named constant: its name, its module, its docstring, and its position if a constructor. -/
def named (n : Name) : MetaM Json := do
  let env ← getEnv
  let mod := (env.getModuleIdxFor? n).map fun i ↦ env.header.moduleNames[i.toNat]!
  return Json.mkObj [("name", toJson n.toString),
    ("module", toJson ((mod.map Name.toString).getD "")),
    ("doc", toJson ((← findDocString? env n).getD "")), ("rank", toJson (← rank n))]

/-- The constant a term names: a constant, or the constructor that indexes it, as the account in
`Account.theory a` or the accommodation in `Accommodation.parser p`. -/
def nameOf (e : Expr) : MetaM Name := do
  let e := e.consumeMData
  if let .const n _ := e then return n
  match e.getAppArgs.back? with
  | some (.const n _) => return n
  | _ => throwError "cannot name {e}"

/-- A theory, and the variant it is scored with if it is a pair. -/
def theoryOf (T : Expr) : MetaM (Name × Option Name) := do
  if T.isAppOfArity ``Prod.mk 4 then
    return (← nameOf T.appFn!.appArg!, some (← nameOf T.appArg!))
  return (← nameOf T, none)

/-- The theory of a scored pair, or the term itself. -/
def theoryTerm (T : Expr) : Expr :=
  if T.isAppOfArity ``Prod.mk 4 then T.appFn!.appArg! else T

/-- The components of a cell: a constructor, a tuple of them, or `()`. -/
partial def cellOf (c : Expr) : MetaM (List Name) := do
  let c := c.consumeMData
  if c.isAppOfArity ``Prod.mk 4 then
    return (← cellOf c.appFn!.appArg!) ++ (← cellOf c.appArg!)
  if c.isConstOf ``PUnit.unit || c.isConstOf ``Unit.unit then return []
  return [← nameOf c]

/-- The conjuncts of a statement. -/
partial def conjuncts (e : Expr) : MetaM (List Expr) := do
  match (← whnfR e).and? with
  | some (a, b) => return (← conjuncts a) ++ (← conjuncts b)
  | none => return [e]

/-- Every assignment of constructors to the variables. -/
def assignments : List (List Name) → List (List Expr)
  | [] => [[]]
  | cs :: rest => cs.flatMap fun c ↦ (assignments rest).map (mkConst c :: ·)

/-- Whether a statement is a claim the export reads. -/
def isClaim (e : Expr) : Bool :=
  match e.eq? with
  | some (_, l, _) => l.isAppOfArity `Eval.Experiment.verdict 7 ||
      l.isAppOfArity `Eval.Experiment.observed 5 || l.isAppOfArity `Eval.Parser.stipulations 4 ||
      l.isAppOfArity `Eval.Parser.parse 6
  | none => false

/-- What the export collects. -/
structure Out where
  verdicts : Array Json := #[]
  observed : Array Json := #[]
  stipulations : Array Json := #[]
  sameParse : Array Json := #[]
  names : Std.HashSet Name := {}
  /-- Each theory scored, with a term for it. -/
  theories : Std.HashMap Name Expr := {}

/-- Read one claim, instantiated. -/
def readClaim (thm : Name) (claim : Expr) (out : Out) : MetaM Out := do
  let some (_, l, r) := claim.eq? | return out
  let src := toJson thm.toString
  let args := l.getAppArgs
  if l.isAppOfArity `Eval.Experiment.verdict 7 then
    let X ← nameOf args[4]!
    let (T, v) ← theoryOf args[5]!
    let c ← cellOf args[6]!
    let names := ((c ++ v.toList).foldl (·.insert ·) out.names).insert X |>.insert T
    let theories := if out.theories.contains T then out.theories
      else out.theories.insert T (theoryTerm args[5]!)
    return { out with names, theories, verdicts := out.verdicts.push <| Json.mkObj [
      ("experiment", toJson X.toString), ("theory", toJson T.toString),
      ("variant", toJson (v.map Name.toString)), ("cell", toJson (c.map Name.toString)),
      ("verdict", ← ctorTree r), ("theorem", src)] }
  if l.isAppOfArity `Eval.Experiment.observed 5 then
    let X ← nameOf args[3]!
    let c ← cellOf args[4]!
    return { out with observed := out.observed.push <| Json.mkObj [
      ("experiment", toJson X.toString), ("cell", toJson (c.map Name.toString)),
      ("observed", ← ctorTree r), ("theorem", src)] }
  if l.isAppOfArity `Eval.Parser.stipulations 4 then
    let v ← nameOf args[3]!
    let sentences ← (← literalElems r).mapM nameOf
    let row := Json.mkObj [("variant", toJson v.toString),
      ("sentences", toJson (sentences.map Name.toString)), ("theorem", src)]
    return { out with names := out.names.insert v, stipulations := out.stipulations.push row }
  let some π' := r.getAppArgs[3]? | throwError "not a parse: {r}"
  return { out with sameParse := out.sameParse.push <| Json.mkObj [
    ("variant", toJson (← nameOf args[3]!).toString), ("as", toJson (← nameOf π').toString),
    ("theorem", src)] }

/-- Read one theorem, if it is a claim about experiments or parsers whose variables range over
enumerations. -/
def readTheorem (thm : Name) (ty : Expr) (out : Out) : MetaM Out :=
  forallTelescope ty fun xs body ↦ do
    let mut ctors := []
    for x in xs do
      let some cs ← enumCtors (← inferType x) | return out
      ctors := ctors ++ [cs]
    let claims ← conjuncts body
    unless claims.all isClaim do return out
    if (← collectAxioms thm).contains ``sorryAx then throwError "{thm} depends on sorry"
    let mut out := { out with names := out.names.insert thm }
    for vals in assignments ctors do
      for claim in claims do
        out ← readClaim thm (claim.replaceFVars xs vals.toArray) out
    return out

/-- Read every theorem of the libraries. -/
def exportAll : MetaM Json := do
  let env ← getEnv
  let mut out : Out := {}
  for (n, info) in env.constants.map₁.toList do
    let .thmInfo t := info | continue
    if n.isInternal then continue
    let some i := env.getModuleIdxFor? n | continue
    unless libraries.contains env.header.moduleNames[i.toNat]!.getRoot.toString do continue
    out ← readTheorem n t.type out
  let defs ← definitions (out.theories.toList.mergeSort (·.1.toString ≤ ·.1.toString))
  let all := defs.foldl (fun s (_, ns) ↦ ns.foldl (·.insert ·) s) out.names
  let names ← all.toList.mapM fun n ↦ return (n.toString, ← named n)
  return Json.mkObj [("verdicts", toJson out.verdicts), ("observed", toJson out.observed),
    ("stipulations", toJson out.stipulations), ("sameParse", toJson out.sameParse),
    ("definitions", Json.mkObj (defs.map fun (T, ns) ↦ (T.toString, toJson (ns.map toString)))),
    ("names", Json.mkObj names)]

end EvalPage

#eval show MetaM Unit from do
  let path := (← IO.getEnv "EVAL_PAGE_JSON").getD ".lake/build/eval-page/verdicts.json"
  if let some dir := (System.FilePath.mk path).parent then IO.FS.createDirAll dir
  IO.FS.writeFile path (← EvalPage.exportAll).pretty
