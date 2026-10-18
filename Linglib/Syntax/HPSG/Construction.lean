/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.HPSG.Description
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.FinCases

/-!
# The construct hierarchy of Sign-Based Construction Grammar in RSRL

A construct pairs a mother sign with daughter signs, and a construction is a constraint on the
constructs of one sort. Construct sorts are classified by how they are headed and by the kind of
clause they form. A sort below one sort of each dimension inherits the constraints on both,
since a constraint on a sort holds of every entity below it. This file states in RSRL the
fragment of Sign-Based Construction Grammar with which Sag analyses the English filler-gap
clauses.

The headed construction gives the mother the category of its head daughter. The filler-head
construction identifies the filler daughter with the first sign on the head daughter's `GAP`
list and passes the rest of the list to the mother. Each filler-gap clause adds constraints on
its daughters, the clause types fix the semantic type of the mother after Ginzburg and Sag, and
the topicalized, wh-exclamative and the-clause constructions give the head daughter exactly one
gap. The principle `memberDef` defines list membership, uniquely on lists without cycles.

## Main definitions

* `HPSG.Construction.Srt`: the sorts, with the hierarchies of categories, semantic types, lists,
  signs, constructs and clauses.
* `HPSG.Construction.sig`: the signature.
* `HPSG.Construction.fillerHeadPrinciple`: the filler-head construction.
* `HPSG.Construction.constraints`: the constructions, each a constraint on one sort.
* `HPSG.Construction.grammar`: the grammar that states the constructions.
* `HPSG.Construction.ListMem`: the elements of a list in an interpretation.
* `HPSG.Construction.memberDef`: the principle that defines list membership.

## Main results

* `HPSG.Construction.forall_satisfies_grammar_iff_of_nsWhIntCl`: a nonsubject wh-interrogative
  satisfies the grammar exactly when it satisfies the four constructions it inherits.
* `HPSG.Construction.satisfies_mtrGap_iff`: in a model of the grammar, the mother of a
  filler-head construct has the `GAP` list that remains of its head daughter's.
* `HPSG.Construction.not_le_covertExpr`: no daughter of a construct is covert.
* `HPSG.Construction.models_memberDef_iff`: on lists without cycles, a well-typed interpretation
  models `memberDef` exactly when `member` is list membership.

## Implementation notes

As in Sag's grammars, a `GAP` list contains signs. Signs are overt or covert, only overt signs
are daughters of constructs, and a word leaves a covert sign of sort `gap` on its `GAP` list for
an argument that it does not realize. The features of `SYN` and the index of `SEM` are attributes
of the sign itself. The filler-head construction identifies the `SYN` value of the filler with
that of the gap except for `WH` and `REL`, which are not in the signature, so the filler and the
gap share their `CAT` and `GAP` values, and, in Sag's synopsis of the framework, their index.
Daughters are attributes named by their role rather than members of a `DTRS` list. `WH`, `REL`, `IC`, `VFORM`, `VAL`,
`STORE` and compositional semantics are not in the signature, and the semantic type of the
mother stands in for its meaning. Sag places the topicalized clause below the filler-head
construct alone and gives its head daughter an austinean meaning, which the mother's meaning
inherits; here the mother's type is stated.

The aux-initial sorts and `INV` are constrained in `Studies/SagEtAl2020`, the coordinate
construct in `Studies/SagWasowBender2003`, and the island status of the five filler-gap clauses
is derived in `Studies/Sag2010`.

## References

* [sag-2010]
* [sag-2012]
* [sag-etal-2020]
* [ginzburg-sag-2000]
* [sag-wasow-bender-2003]
* [richter-2024]
-/

@[expose] public section

namespace HPSG.Construction

open HPSG.RSRL

/-! ### Sorts -/

/-- The sorts of the fragment. -/
inductive Srt
  | top
  -- categories
  | cat | verbal | nonverbal | verb | comp | nominal | noun | prep | adj | adv
  -- semantic types
  | semType | austinean | question | fact | modifier
  -- inversion values
  | invVal | invPlus | invMinus
  -- lists and indices
  | list | elist | nelist | idx
  -- signs
  | sign | overtExpr | covertExpr | gap
  -- constructs
  | construct | phrasalCxt | headedCxt | clause | coordCxt | fillerHeadCxt | auxInitialCxt
  -- clause types
  | coreCl | relativeCl | declarativeCl | interrogativeCl | exclamativeCl
  -- clauses that are headed constructs
  | topCl | whExclCl | nsWhIntCl | whRelCl | theCl | polarIntCl | auxInitialExclCl
  deriving DecidableEq, Fintype, Repr

/-- The immediate supersorts of a sort. Each filler-gap clause other than the topicalized clause
and each aux-initial clause has two, a headed construct and a clause type. -/
def Srt.parents : Srt → List Srt
  | .top => []
  | .cat | .semType | .invVal | .list | .idx | .sign | .construct => [.top]
  | .verbal | .nonverbal => [.cat]
  | .verb | .comp => [.verbal]
  | .nominal | .adj | .adv => [.nonverbal]
  | .noun | .prep => [.nominal]
  | .austinean | .question | .fact | .modifier => [.semType]
  | .invPlus | .invMinus => [.invVal]
  | .elist | .nelist => [.list]
  | .overtExpr | .covertExpr => [.sign]
  | .gap => [.covertExpr]
  | .phrasalCxt => [.construct]
  | .headedCxt | .clause | .coordCxt => [.phrasalCxt]
  | .fillerHeadCxt | .auxInitialCxt => [.headedCxt]
  | .coreCl | .relativeCl => [.clause]
  | .declarativeCl | .interrogativeCl | .exclamativeCl => [.coreCl]
  | .topCl => [.fillerHeadCxt]
  | .theCl => [.fillerHeadCxt, .declarativeCl]
  | .whExclCl => [.fillerHeadCxt, .exclamativeCl]
  | .nsWhIntCl => [.fillerHeadCxt, .interrogativeCl]
  | .whRelCl => [.fillerHeadCxt, .relativeCl]
  | .polarIntCl => [.auxInitialCxt, .interrogativeCl]
  | .auxInitialExclCl => [.auxInitialCxt, .exclamativeCl]

/-- The length of the longest chain from a sort up to `top`. -/
def Srt.rank : Srt → ℕ
  | .top => 0
  | .cat | .semType | .invVal | .list | .idx | .sign | .construct => 1
  | .verbal | .nonverbal | .austinean | .question | .fact | .modifier | .invPlus | .invMinus
  | .elist | .nelist | .overtExpr | .covertExpr | .phrasalCxt => 2
  | .verb | .comp | .nominal | .adj | .adv | .gap | .headedCxt | .clause | .coordCxt => 3
  | .noun | .prep | .fillerHeadCxt | .auxInitialCxt | .coreCl | .relativeCl => 4
  | .declarativeCl | .interrogativeCl | .exclamativeCl | .topCl => 5
  | .whExclCl | .nsWhIntCl | .whRelCl | .theCl | .polarIntCl | .auxInitialExclCl => 6

instance : PartialOrder Srt :=
  partialOrderOfCovers (fun σ τ : Srt ↦ τ ∈ σ.parents) Srt.rank (by decide)

instance : DecidableLE Srt :=
  Relation.ReflTransGen.decidable_of_fintype_step (fun σ ↦ σ.parents.toFinset) (by simp)

/-! ### Attributes and the signature -/

/-- The attributes. A construct has a mother and daughters, a sign has a category, a `GAP` list,
a semantic type, an inversion value and an index, and a nonempty list has a first element and a
rest. -/
inductive Attr
  | MTR | HDDTR | FILLERDTR | CONJ1 | CONJ2 | CAT | GAP | SEM | INV | INDEX | FIRST | REST
  deriving DecidableEq, Fintype, Repr

/-- The sorts that introduce each attribute, with its value sort there. The mother of a phrasal
construct and its daughters are overt, and a list contains signs. -/
def Attr.decl : Attr → List (Srt × Srt)
  | .MTR => [(.phrasalCxt, .overtExpr)]
  | .HDDTR => [(.headedCxt, .overtExpr)]
  | .FILLERDTR => [(.fillerHeadCxt, .overtExpr)]
  | .CONJ1 | .CONJ2 => [(.coordCxt, .overtExpr)]
  | .CAT => [(.sign, .cat)]
  | .GAP => [(.sign, .list)]
  | .SEM => [(.sign, .semType)]
  | .INV => [(.sign, .invVal)]
  | .INDEX => [(.sign, .idx)]
  | .FIRST => [(.nelist, .sign)]
  | .REST => [(.nelist, .list)]

/-- The one relation symbol is list membership. -/
inductive Rel | member
  deriving DecidableEq, Fintype, Repr

/-- The signature of the fragment. -/
@[reducible] def sig : Signature Srt := .ofDecl Attr Rel (fun _ ↦ 2) Attr.decl (by decide +kernel)

/-- A nonsubject wh-interrogative construct inherits its mother from the phrasal construct and
its filler daughter from the filler-head construct, and a coordinate construct has no filler
daughter. -/
example : sig.approp .nsWhIntCl .MTR = some .overtExpr ∧
    sig.approp .nsWhIntCl .FILLERDTR = some .overtExpr ∧
    sig.approp .coordCxt .FILLERDTR = none := by decide

/-- The interpretation of `member` that holds of nothing, for models whose principles do not
mention the relation. -/
def noRel {U : Type*} (ρ : sig.Rel) : Set (Fin (sig.arity ρ) → U) := ∅

instance {U : Type*} (ρ : sig.Rel) : DecidablePred (@noRel U ρ) := fun _ ↦ instDecidableFalse

/-! ### Constructions -/

/-- The headed construction of [sag-2010]: the mother of a headed construct has the category of
its head daughter. -/
def headedPrinciple : Constraint sig :=
  ⟨.headedCxt, .pathEq (.path [.MTR, .CAT]) (.path [.HDDTR, .CAT])⟩

/-- The filler-head construction ([sag-2010] (58), [sag-2012] (141)). The head daughter is
verbal. The filler daughter shares its category, its `GAP` list and its index with the first
sign on the head daughter's `GAP` list, and the mother's `GAP` list is the rest of the head
daughter's. -/
def fillerHeadPrinciple : Constraint sig where
  sort := .fillerHeadCxt
  body :=
    .and (.sortAssign (.path [.HDDTR, .CAT]) .verbal)
      (.and (.pathEq (.path [.FILLERDTR, .CAT]) (.path [.HDDTR, .GAP, .FIRST, .CAT]))
        (.and (.pathEq (.path [.FILLERDTR, .GAP]) (.path [.HDDTR, .GAP, .FIRST, .GAP]))
          (.and (.pathEq (.path [.FILLERDTR, .INDEX]) (.path [.HDDTR, .GAP, .FIRST, .INDEX]))
            (.pathEq (.path [.MTR, .GAP]) (.path [.HDDTR, .GAP, .REST])))))

/-- The mother of a declarative clause has an austinean semantic type. -/
def declarativePrinciple : Constraint sig :=
  ⟨.declarativeCl, .sortAssign (.path [.MTR, .SEM]) .austinean⟩

/-- The mother of an interrogative clause denotes a question. -/
def interrogativePrinciple : Constraint sig :=
  ⟨.interrogativeCl, .sortAssign (.path [.MTR, .SEM]) .question⟩

/-- The mother of an exclamative clause denotes a fact. -/
def exclamativePrinciple : Constraint sig :=
  ⟨.exclamativeCl, .sortAssign (.path [.MTR, .SEM]) .fact⟩

/-- The topicalization construction ([sag-2010] (61)). The filler daughter is nonverbal, the
head daughter is a projection of a verb with exactly one gap, which excludes the
complementizer-headed clause that a the-clause allows, and the mother is austinean. -/
def topPrinciple : Constraint sig :=
  ⟨.topCl, .and (.sortAssign (.path [.FILLERDTR, .CAT]) .nonverbal)
    (.and (.sortAssign (.path [.HDDTR, .CAT]) .verb)
      (.and (.sortAssign (.path [.HDDTR, .GAP, .REST]) .elist)
        (.sortAssign (.path [.MTR, .SEM]) .austinean)))⟩

/-- The wh-exclamative construction ([sag-2010] (70)). The filler daughter is nonverbal and the
head daughter has exactly one gap. -/
def whExclPrinciple : Constraint sig :=
  ⟨.whExclCl, .and (.sortAssign (.path [.FILLERDTR, .CAT]) .nonverbal)
    (.sortAssign (.path [.HDDTR, .GAP, .REST]) .elist)⟩

/-- The nonsubject wh-interrogative construction ([sag-2010] (80)) requires a nonverbal filler
daughter. -/
def nsWhIntPrinciple : Constraint sig :=
  ⟨.nsWhIntCl, .sortAssign (.path [.FILLERDTR, .CAT]) .nonverbal⟩

/-- The wh-relative construction ([sag-2010] (90), (92)). Its finite and infinitival subtypes
require a nominal and a prepositional filler daughter, so the filler daughter is nominal, and
the mother has the semantic type of a modifier. -/
def whRelPrinciple : Constraint sig :=
  ⟨.whRelCl, .and (.sortAssign (.path [.FILLERDTR, .CAT]) .nominal)
    (.sortAssign (.path [.MTR, .SEM]) .modifier)⟩

/-- The the-clause construction ([sag-2010] (108)). The filler daughter is nonverbal and the head
daughter has exactly one gap. -/
def thePrinciple : Constraint sig :=
  ⟨.theCl, .and (.sortAssign (.path [.FILLERDTR, .CAT]) .nonverbal)
    (.sortAssign (.path [.HDDTR, .GAP, .REST]) .elist)⟩

/-- The constructions of the fragment. -/
def constraints : List (Constraint sig) :=
  [headedPrinciple, fillerHeadPrinciple, declarativePrinciple, interrogativePrinciple,
    exclamativePrinciple, topPrinciple, whExclPrinciple, nsWhIntPrinciple, whRelPrinciple,
    thePrinciple]

/-- The grammar of the fragment. -/
def grammar : Grammar sig := constraints.map Constraint.toDesc

/-- Every principle of the grammar is closed, so its satisfaction does not depend on the
variable assignment. -/
theorem freeVars_grammar : ∀ d ∈ grammar, d.freeVars = ∅ := by decide

/-- The signature admits the paths of the filler-head construction from the sort it constrains,
and it admits no filler daughter in a coordinate construct. -/
example : sig.Admits .fillerHeadCxt [.HDDTR, .GAP, .FIRST, .INDEX] .idx ∧
    sig.Admits .fillerHeadCxt [.HDDTR, .GAP, .REST] .elist ∧
    ¬ ∃ ρ, sig.Admits .coordCxt [.FILLERDTR, .CAT] ρ := by decide +kernel

/-! ### Inheritance -/

/-- Each filler-gap clause inherits the headed and filler-head constructions, and the clause
type of every clause but the topicalized one, and has a construction of its own. -/
theorem map_sort_inherited_fillerGap :
    (Constraint.inherited constraints .topCl).map (·.sort) =
        [.headedCxt, .fillerHeadCxt, .topCl] ∧
      (Constraint.inherited constraints .whExclCl).map (·.sort) =
        [.headedCxt, .fillerHeadCxt, .exclamativeCl, .whExclCl] ∧
      (Constraint.inherited constraints .nsWhIntCl).map (·.sort) =
        [.headedCxt, .fillerHeadCxt, .interrogativeCl, .nsWhIntCl] ∧
      (Constraint.inherited constraints .whRelCl).map (·.sort) =
        [.headedCxt, .fillerHeadCxt, .whRelCl] ∧
      (Constraint.inherited constraints .theCl).map (·.sort) =
        [.headedCxt, .fillerHeadCxt, .declarativeCl, .theCl] := by
  decide

variable {U : Type*} {I : Interpretation sig U} {g : ℕ → U} {u : U}

/-- An entity of the nonsubject wh-interrogative sort satisfies the grammar exactly when it
satisfies the headed, filler-head, interrogative and nonsubject wh-interrogative constructions.
Only the last is stated on its sort. -/
theorem forall_satisfies_grammar_iff_of_nsWhIntCl (hu : I.S u = .nsWhIntCl) :
    (∀ d ∈ grammar, I.Satisfies g u d) ↔
      ∀ c ∈ [headedPrinciple, fillerHeadPrinciple, interrogativePrinciple, nsWhIntPrinciple],
        I.Satisfies g u c.body := by
  rw [grammar, Interpretation.forall_satisfies_map_toDesc_iff, hu]
  rfl

/-- In a model of the grammar, the mother of a filler-head construct has a `GAP` list of sort
`σ` exactly when the rest of its head daughter's list does, since the filler discharges the
first gap and the rest passes up. The mother's list is therefore empty exactly when the head
daughter has one gap. -/
theorem satisfies_mtrGap_iff (hI : I.Models grammar) (hu : I.S u ≤ .fillerHeadCxt) (σ : Srt) :
    I.Satisfies (fun _ ↦ u) u (.sortAssign (.path [.MTR, .GAP]) σ) ↔
      I.Satisfies (fun _ ↦ u) u (.sortAssign (.path [.HDDTR, .GAP, .REST]) σ) := by
  obtain ⟨-, -, -, -, v, hv, hv'⟩ :=
    hI.satisfies_body (c := fillerHeadPrinciple) (List.mem_map_of_mem (by simp [constraints])) hu
  simp only [Interpretation.satisfies_sortAssign]
  constructor <;> rintro ⟨w, hw, hle⟩
  · obtain rfl : w = v := Option.mem_unique hw hv
    exact ⟨w, hv', hle⟩
  · obtain rfl : w = v := Option.mem_unique hw hv'
    exact ⟨w, hv, hle⟩

/-- No daughter or mother of a construct is covert in a well-typed interpretation, since the
signs of a phrasal construct are overt expressions [sag-2012]. A gap, which stands on a `GAP`
list for an unrealized argument, is therefore never a daughter. -/
theorem not_le_covertExpr (hI : I.IsWellTyped) {α : sig.Attr}
    (hα : α ∈ [.MTR, .HDDTR, .FILLERDTR, .CONJ1, .CONJ2]) {v : U} (hv : I.A α u = some v) :
    ¬ I.S v ≤ .covertExpr := by
  obtain ⟨τ, hτ, hle⟩ := hI α u v hv
  obtain ⟨d, hd, -, rfl⟩ := exists_mem_decl_of_appropOfDecl_eq_some _ hτ
  rw [(by decide : ∀ α ∈ ([.MTR, .HDDTR, .FILLERDTR, .CONJ1, .CONJ2] : List Attr),
    ∀ d ∈ Attr.decl α, d.2 = .overtExpr) α hα d hd] at hle
  exact (by decide +kernel : ∀ σ : Srt, σ ≤ .overtExpr → ¬ σ ≤ .covertExpr) _ hle

/-! ### Models of filler-head constructs -/

/-- The entities of the worked constructs are the construct, its mother, head daughter and
filler daughter, four categories, two list cells and the empty list, the category of a second
gap, a semantic object, and two gaps with their indices. -/
inductive Ent
  | cxt | mtr | hd | fl | npCat | vpCat | adjCat | compCat | g1 | g2 | nil | c2 | sem
  | gp1 | gp2 | ix1 | ix2
  deriving DecidableEq, Fintype, Repr

/-- The default sort of each entity. A model overrides the sort of the construct and, where its
clause type requires, of the semantic object and of the second gap's category. -/
def baseS : Ent → Srt
  | .cxt => .fillerHeadCxt
  | .mtr | .hd | .fl => .overtExpr
  | .npCat | .c2 => .noun
  | .vpCat => .verb
  | .adjCat => .adj
  | .compCat => .comp
  | .g1 | .g2 => .nelist
  | .nil => .elist
  | .sem => .austinean
  | .gp1 | .gp2 => .gap
  | .ix1 | .ix2 => .idx

/-- The attribute values of a construct with one gap. The head daughter and the mother are
verbal, the head daughter has the `GAP` list `⟨gp1⟩`, the filler is a noun phrase that shares its
category, its empty `GAP` list and its index with `gp1`, and the mother's `GAP` list is empty. -/
def singleGapA : Attr → Ent → Option Ent
  | .MTR, .cxt => some .mtr
  | .HDDTR, .cxt => some .hd
  | .FILLERDTR, .cxt => some .fl
  | .CAT, .fl | .CAT, .gp1 => some .npCat
  | .INDEX, .fl | .INDEX, .gp1 => some .ix1
  | .CAT, .hd | .CAT, .mtr => some .vpCat
  | .GAP, .hd => some .g1
  | .FIRST, .g1 => some .gp1
  | .REST, .g1 | .GAP, .mtr | .GAP, .fl | .GAP, .gp1 => some .nil
  | .SEM, .mtr => some .sem
  | _, _ => none

/-- The attribute values of a construct whose head daughter has the `GAP` list `⟨gp1, gp2⟩`. The
filler discharges `gp1`, and the mother's `GAP` list is the rest, `⟨gp2⟩`. -/
def twoGapA : Attr → Ent → Option Ent
  | .MTR, .cxt => some .mtr
  | .HDDTR, .cxt => some .hd
  | .FILLERDTR, .cxt => some .fl
  | .CAT, .fl | .CAT, .gp1 => some .npCat
  | .INDEX, .fl | .INDEX, .gp1 => some .ix1
  | .CAT, .hd | .CAT, .mtr => some .vpCat
  | .GAP, .hd => some .g1
  | .FIRST, .g1 => some .gp1
  | .REST, .g1 | .GAP, .mtr => some .g2
  | .FIRST, .g2 => some .gp2
  | .CAT, .gp2 => some .c2
  | .INDEX, .gp2 => some .ix2
  | .REST, .g2 | .GAP, .fl | .GAP, .gp1 | .GAP, .gp2 => some .nil
  | .SEM, .mtr => some .sem
  | _, _ => none

/-- The model of a construct of sort `cxtSort` whose mother has semantic type `semSort`, with
the attribute values `a`. -/
@[reducible] def singleConstruct (cxtSort semSort : Srt) (a : Attr → Ent → Option Ent) :
    Interpretation sig Ent where
  S
    | .cxt => cxtSort
    | .sem => semSort
    | u => baseS u
  A := a
  R := noRel

/-- The model of a two-gap construct of sort `cxtSort` whose mother has semantic type `semSort`
and whose second gap has category `c2Sort`. -/
@[reducible] def twoGapConstruct (cxtSort semSort c2Sort : Srt) : Interpretation sig Ent where
  S
    | .cxt => cxtSort
    | .sem => semSort
    | .c2 => c2Sort
    | u => baseS u
  A := twoGapA
  R := noRel

/-- A well-formed filler-head construct with one gap. -/
abbrev goodFillerHead : Interpretation sig Ent :=
  singleConstruct .fillerHeadCxt .austinean singleGapA

example : goodFillerHead.Models grammar := by decide +kernel

/-- A filler-head construct whose mother is a noun phrase although its head daughter is verbal.
It violates the headed construction. -/
abbrev mtrCatMismatch : Interpretation sig Ent :=
  singleConstruct .fillerHeadCxt .austinean fun
    | .CAT, .mtr => some .npCat
    | a, u => singleGapA a u

example : mtrCatMismatch.Models [fillerHeadPrinciple] ∧
    ¬ mtrCatMismatch.Models [headedPrinciple] := by decide

/-- A filler-head construct whose filler is an adjective phrase although the gap is a noun
phrase, so the identity of their categories fails. -/
abbrev gapMismatch : Interpretation sig Ent :=
  singleConstruct .fillerHeadCxt .austinean fun
    | .CAT, .fl => some .adjCat
    | a, u => singleGapA a u

example : ¬ gapMismatch.Models [fillerHeadPrinciple] := by decide

/-- A filler-head construct whose filler and gap agree in category but differ in index. -/
abbrev indexMismatch : Interpretation sig Ent :=
  singleConstruct .fillerHeadCxt .austinean fun
    | .INDEX, .fl => some .ix2
    | a, u => singleGapA a u

example : ¬ indexMismatch.Models [fillerHeadPrinciple] := by decide

/-- A filler-head construct whose filler has a `GAP` list of its own, which the gap it fills does
not share. -/
abbrev fillerGapMismatch : Interpretation sig Ent :=
  singleConstruct .fillerHeadCxt .austinean fun
    | .GAP, .fl => some .g1
    | a, u => singleGapA a u

example : ¬ fillerGapMismatch.Models [fillerHeadPrinciple] := by decide

/-- A filler-head construct whose head daughter has two gaps. The second gap passes to the
mother. -/
abbrev goodTwoGap : Interpretation sig Ent :=
  twoGapConstruct .fillerHeadCxt .austinean .noun

example : goodTwoGap.Models grammar := by decide +kernel

/-- A well-formed nonsubject wh-interrogative construct. -/
abbrev goodNsWhInt : Interpretation sig Ent :=
  singleConstruct .nsWhIntCl .question singleGapA

example : goodNsWhInt.Models grammar := by decide +kernel

/-- A nonsubject wh-interrogative construct whose mother has an austinean semantic type. It
violates the constraint that it inherits from the interrogative clause. -/
abbrev nsWhIntWrongSem : Interpretation sig Ent :=
  singleConstruct .nsWhIntCl .austinean singleGapA

example : nsWhIntWrongSem.Models [fillerHeadPrinciple] ∧
    ¬ nsWhIntWrongSem.Models [interrogativePrinciple] := by decide

/-- A wh-relative construct whose filler is an adjective phrase that matches the gap. It
satisfies the filler-head construction but not the requirement of a nominal filler. -/
abbrev whRelAdjFiller : Interpretation sig Ent :=
  singleConstruct .whRelCl .modifier fun
    | .CAT, .fl | .CAT, .gp1 => some .adjCat
    | a, u => singleGapA a u

example : whRelAdjFiller.Models [fillerHeadPrinciple] ∧
    ¬ whRelAdjFiller.Models [whRelPrinciple] := by decide

/-- A the-clause whose head daughter is headed by a complementizer. -/
abbrev goodTheCl : Interpretation sig Ent :=
  singleConstruct .theCl .austinean fun
    | .CAT, .hd | .CAT, .mtr => some .compCat
    | a, u => singleGapA a u

example : goodTheCl.Models grammar := by decide +kernel

/-- A the-clause whose head daughter has two gaps. The the-clause construction gives the head
daughter one gap, so the grammar rejects it, as it accepts the same construct of the
filler-head sort. -/
example : ¬ (twoGapConstruct .theCl .austinean .noun).Models grammar := by decide +kernel

/-- A topicalized clause whose head daughter is headed by a complementizer. The head is verbal,
as the filler-head construction requires, but it is not a projection of a verb. -/
abbrev topClCompHead : Interpretation sig Ent :=
  singleConstruct .topCl .austinean fun
    | .CAT, .hd | .CAT, .mtr => some .compCat
    | a, u => singleGapA a u

example : topClCompHead.Models [fillerHeadPrinciple] ∧ ¬ topClCompHead.Models [topPrinciple] := by
  decide

/-! ### The `GAP` list as a set

The filler-head construction discharges the first sign on the `GAP` list. The relation
`member`, which `memberDef` defines, lets a principle speak of any element instead. -/

/-- The entity `x` is an element of the list `l` when some cell that `REST` reaches from `l` has
`x` as its first element. -/
def ListMem (I : Interpretation sig U) (x l : U) : Prop :=
  ∃ c, Relation.ReflTransGen (fun a b ↦ I.A .REST a = some b) l c ∧ I.A .FIRST c = some x

instance [Fintype U] [DecidableEq U] (x l : U) : Decidable (ListMem I x l) := by
  unfold ListMem; infer_instance

/-- An element of a list is the first element or an element of the rest. -/
theorem listMem_iff {x l : U} :
    ListMem I x l ↔ I.A .FIRST l = some x ∨ ∃ y, I.A .REST l = some y ∧ ListMem I x y := by
  constructor
  · rintro ⟨c, hc, hx⟩
    rcases Relation.ReflTransGen.cases_head hc with rfl | ⟨y, hy, hyc⟩
    · exact .inl hx
    · exact .inr ⟨y, hy, c, hyc, hx⟩
  · rintro (hx | ⟨y, hy, c, hyc, hx⟩)
    · exact ⟨l, .refl, hx⟩
    · exact ⟨c, .head hy hyc, hx⟩

/-- The principle that defines `member`. The entity `x` is a member of `L` exactly when `L` is a
nonempty list and `x` is its first element or a member of its rest. The rest reaches the
relation through the bound variable `2`, since a relation symbol applies to variables. -/
def memberDef : Desc sig :=
  .all 0 (.all 1 (.iff (.rel .member ![0, 1])
    (.and (.sortAssign (.var 1) .nelist)
      (.or (.pathEq (.var 0) (.feat (.var 1) .FIRST))
        (.ex 2 (.and (.pathEq (.var 2) (.feat (.var 1) .REST)) (.rel .member ![0, 2])))))))

/-- An entity satisfies `memberDef` when `member` relates two of its components exactly as
the principle says, the rest of a list being a component wherever the list is. -/
theorem satisfies_memberDef_iff : I.Satisfies g u memberDef ↔
    ∀ x, I.IsComponentOf u x → ∀ l, I.IsComponentOf u l →
      (I.R .member ![x, l] ↔ I.S l ≤ .nelist ∧
        (I.A .FIRST l = some x ∨ ∃ y, I.A .REST l = some y ∧ I.R .member ![x, y])) := by
  have e01 (x l : U) :
      (fun i ↦ Function.update (Function.update g 0 x) 1 l (![0, 1] i)) = ![x, l] := by
    funext i; fin_cases i <;> rfl
  have e02 (x l y : U) : (fun i ↦ Function.update (Function.update (Function.update g 0 x) 1 l) 2 y
      (![0, 2] i)) = ![x, y] := by
    funext i; fin_cases i <;> rfl
  have u0 (x l : U) : Function.update (Function.update g 0 x) 1 l 0 = x := rfl
  have u1 (x l y : U) : Function.update (Function.update (Function.update g 0 x) 1 l) 2 y 1 = l :=
    rfl
  simp only [memberDef, Interpretation.satisfies_all, Interpretation.satisfies_iff,
    Interpretation.satisfies_and, Interpretation.satisfies_or, Interpretation.satisfies_rel,
    Interpretation.satisfies_sortAssign, Interpretation.satisfies_pathEq,
    Interpretation.satisfies_ex, Interpretation.termDenot_var, Interpretation.termDenot_feat,
    e01, e02]
  simp only [Function.update_self, Option.mem_def, Option.bind_some, Option.some.injEq,
    exists_eq_left', u0, u1]
  exact forall_congr' fun _ ↦ imp_congr_right fun _ ↦ forall_congr' fun _ ↦
    imp_congr_right fun hl ↦ iff_congr Iff.rfl <| and_congr_right fun _ ↦ or_congr_right <|
      exists_congr fun _ ↦ ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hl.tail ⟨_, h.1⟩, h⟩⟩

/-- An attribute of a list cell is defined only on a nonempty list in a well-typed
interpretation. -/
private theorem le_nelist_of_A {α : sig.Attr} (hI : I.IsWellTyped) (hα : α = .FIRST ∨ α = .REST)
    {l v : U} (h : I.A α l = some v) : I.S l ≤ .nelist := by
  obtain ⟨τ, hτ, -⟩ := hI α l v h
  obtain ⟨d, hd, hle, -⟩ := exists_mem_decl_of_appropOfDecl_eq_some _ hτ
  rwa [(by decide : ∀ α ∈ ([.FIRST, .REST] : List Attr), ∀ d ∈ Attr.decl α, d.1 = .nelist) α
    (by rcases hα with rfl | rfl <;> simp) d hd] at hle

/-- In a well-typed interpretation, an element of a list is the first element or an element of
the rest of a nonempty list. -/
private theorem and_or_listMem_iff (hI : I.IsWellTyped) {x l : U} :
    (I.S l ≤ .nelist ∧ (I.A .FIRST l = some x ∨ ∃ y, I.A .REST l = some y ∧ ListMem I x y)) ↔
      ListMem I x l :=
  ⟨fun h ↦ listMem_iff.2 h.2, fun h ↦ ⟨(listMem_iff.1 h).elim (le_nelist_of_A hI (.inl rfl))
    fun ⟨_, hy, _⟩ ↦ le_nelist_of_A hI (.inr rfl) hy, listMem_iff.1 h⟩⟩

/-- A well-typed interpretation models `memberDef` when `member` holds of two components of an
entity just when the first is an element of the second. -/
theorem models_memberDef_of_forall (hI : I.IsWellTyped)
    (h : ∀ u x l, I.IsComponentOf u x → I.IsComponentOf u l →
      (I.R .member ![x, l] ↔ ListMem I x l)) : I.Models [memberDef] := by
  intro u d hd
  rw [List.mem_singleton.1 hd]
  refine satisfies_memberDef_iff.2 fun x hx l hl ↦ ?_
  rw [h u x l hx hl, ← and_or_listMem_iff hI]
  exact and_congr_right fun _ ↦ or_congr_right <| exists_congr fun y ↦
    and_congr_right fun hy ↦ (h u x y hx (hl.tail ⟨_, hy⟩)).symm

/-- On lists without cycles the principle `memberDef` defines list membership. A well-typed
interpretation models it exactly when `member` holds of two components of an entity just when
the first is an element of the second. -/
theorem models_memberDef_iff (hI : I.IsWellTyped)
    (hwf : WellFounded fun b a ↦ I.A .REST a = some b) :
    I.Models [memberDef] ↔ ∀ u x l, I.IsComponentOf u x → I.IsComponentOf u l →
      (I.R .member ![x, l] ↔ ListMem I x l) := by
  refine ⟨fun hM u x l hx hl ↦ ?_, models_memberDef_of_forall hI⟩
  have hu := satisfies_memberDef_iff.1 (hM u _ (List.mem_singleton_self _))
  induction l using hwf.induction with
  | h l ih =>
    rw [hu x hx l hl, ← and_or_listMem_iff hI]
    exact and_congr_right fun _ ↦ or_congr_right <| exists_congr fun y ↦
      and_congr_right fun hy ↦ ih y hy (hl.tail ⟨_, hy⟩)

/-- The entities of a cyclic list are its one cell, whose rest is the cell itself, the cell's
first element, and that element's index. -/
inductive LoopEnt | cell | elem | ix
  deriving DecidableEq, Fintype, Repr

/-- The cyclic list with `member` interpreted as `R`. -/
@[reducible] def loopList (R : LoopEnt → LoopEnt → Prop) : Interpretation sig LoopEnt where
  S
    | .cell => .nelist
    | .elem => .overtExpr
    | .ix => .idx
  A
    | .FIRST, .cell => some .elem
    | .REST, .cell => some .cell
    | .INDEX, .elem => some .ix
    | _, _ => none
  R _ xs := R (xs 0) (xs 1)

instance (R : LoopEnt → LoopEnt → Prop) [DecidableRel R] (ρ : sig.Rel) :
    DecidablePred ((loopList R).R ρ) := fun xs ↦ inferInstanceAs (Decidable (R (xs 0) (xs 1)))

/-- On a cyclic list `memberDef` does not determine `member`. It holds both when the index of the
first element is a member of the list and when it is not, and the index is not an element of the
list. -/
example : (loopList fun x l ↦ x = .elem ∧ l = .cell).Models [memberDef] ∧
    (loopList fun x l ↦ (x = .elem ∨ x = .ix) ∧ l = .cell).Models [memberDef] ∧
    ¬ ListMem (loopList fun _ _ ↦ True) .ix .cell := by
  decide +kernel

/-- The attribute values of a two-gap construct whose filler matches the second element of the
head daughter's `GAP` list in category and index. -/
def secondGapA : Attr → Ent → Option Ent
  | .CAT, .fl => some .c2
  | .INDEX, .fl => some .ix2
  | a, u => twoGapA a u

/-- The two-gap construct whose prepositional filler matches the second gap, with `member`
uninterpreted. -/
@[reducible] def secondGapBase : Interpretation sig Ent where
  S
    | .c2 => .prep
    | u => baseS u
  A := secondGapA
  R := noRel

/-- The same construct with `member` interpreted as list membership. -/
@[reducible] def gapSetModel : Interpretation sig Ent :=
  { secondGapBase with R := fun _ xs ↦ ListMem secondGapBase (xs 0) (xs 1) }

instance (ρ : sig.Rel) : DecidablePred (gapSetModel.R ρ) := fun xs ↦
  inferInstanceAs (Decidable (ListMem secondGapBase (xs 0) (xs 1)))

/-- Some member of the head daughter's `GAP` list shares its category and its index with the
filler. -/
example : gapSetModel.Satisfies (fun _ ↦ .cxt) .cxt
    (.ex 0 (.ex 1 (.and (.pathEq (.var 1) (.path [.HDDTR, .GAP]))
      (.and (.rel .member ![0, 1])
        (.and (.pathEq (.feat (.var 0) .CAT) (.path [.FILLERDTR, .CAT]))
          (.pathEq (.feat (.var 0) .INDEX) (.path [.FILLERDTR, .INDEX]))))))) := by
  decide +kernel

/-- The construct models `memberDef`. -/
example : gapSetModel.Models [memberDef] :=
  models_memberDef_of_forall (by decide +kernel) fun _ _ _ _ _ ↦ Iff.rfl

/-- The same construct violates the filler-head construction, which looks only at the first
element of the list. -/
example : ¬ gapSetModel.Models [fillerHeadPrinciple] := by decide

/-! ### Typing of the models

Every model above is well-typed, so a model that a principle rejects fails that principle and
not the appropriateness conditions. None is totally well-typed, since each interprets only the
attributes that the principles mention. -/

/-- The worked models are well-typed. -/
theorem isWellTyped_models :
    goodFillerHead.IsWellTyped ∧ mtrCatMismatch.IsWellTyped ∧ gapMismatch.IsWellTyped ∧
      indexMismatch.IsWellTyped ∧ fillerGapMismatch.IsWellTyped ∧ goodTwoGap.IsWellTyped ∧
      goodNsWhInt.IsWellTyped ∧ nsWhIntWrongSem.IsWellTyped ∧ whRelAdjFiller.IsWellTyped ∧
      goodTheCl.IsWellTyped ∧ topClCompHead.IsWellTyped ∧ gapSetModel.IsWellTyped := by
  decide +kernel

example : ¬ goodFillerHead.IsTotallyWellTyped := by decide

/-- A model whose `GAP` list contains a category in place of a sign is not well-typed. -/
example : ¬ (singleConstruct .fillerHeadCxt .austinean fun
    | .FIRST, .g1 => some .npCat
    | a, u => singleGapA a u).IsWellTyped := by decide

end HPSG.Construction
