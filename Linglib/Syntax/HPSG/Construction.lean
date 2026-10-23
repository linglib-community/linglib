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
the categories of its daughters and on the inversion, independence and verb form of its head,
the clause types fix the semantic type and verb form of the mother, and the topicalized,
wh-exclamative and the-clause constructions give the head daughter exactly one gap. The
principle `memberDef` defines list membership, uniquely on lists without cycles.

## Main definitions

* `HPSG.Construction.Srt`: the sorts, with the hierarchies of categories, verb forms, semantic
  types, lists, signs, constructs and clauses.
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
* `HPSG.Construction.satisfies_hdCat_iff`: in a model of the grammar, the head daughter of a
  headed construct has the features of its mother's category.
* `HPSG.Construction.not_le_covertExpr`: no daughter of a construct is covert.
* `HPSG.Construction.models_memberDef_iff`: on lists without cycles, a well-typed interpretation
  models `memberDef` exactly when `member` is list membership.

## Implementation notes

As in Sag's grammars, a `GAP` list contains signs. Signs are overt or covert, only overt signs are
daughters of constructs, and a word leaves a covert sign of sort `gap` on its `GAP` list for an
argument that it does not realize. The features of `SYN` and the index of `SEM` are attributes of
the sign itself. The filler-head construction identifies the `SYN` value of the filler with that of
the gap except for `WH` and `REL`, which are not in the signature, so the filler and the gap share
their `CAT` and `GAP` values, and, in Sag's synopsis of the framework, their index. Daughters are
attributes named by their role rather than members of a `DTRS` list. As in Sag's signature, a verbal
category has a verb form and an independence value and a verb an inversion value; of the features he
declares, only those that the constructions here mention are in the signature, so `WH`, `REL`,
`VAL`, `SELECT`, `AUX` and `STORE` are not, and the semantic type of the mother stands in for its
meaning. Sag places the topicalized clause below the filler-head construct alone and gives its head
daughter an austinean meaning, which the mother's meaning inherits; here the mother's type is
stated.

The aux-initial construction is stated in `Studies/SagEtAl2020` and the coordinate construction
in `Studies/SagWasowBender2003`. The worked constructs are in `Studies/Sag2010`, which checks
the paper's judgments against the grammar and derives the island status of the five clauses.

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
  -- verb forms
  | vform | presentPart | perfectPart | passivePart | core | fin | inf | base | gerund
  -- boolean values
  | boolean | plus | minus
  -- semantic types
  | semType | austinean | question | fact | modifier
  -- lists and indices
  | list | elist | nelist | idx
  -- signs
  | sign | overtExpr | covertExpr | gap
  -- constructs
  | construct | phrasalCxt | headedCxt | clause | coordCxt | fillerHeadCxt | auxInitialCxt
  -- clause types
  | coreCl | relativeCl | declarativeCl | interrogativeCl | exclamativeCl
  -- clauses that are headed constructs
  | topCl | whExclCl | nsWhIntCl | whRelCl | finWhRelCl | infWhRelCl | theCl | polarIntCl
  | auxInitialExclCl
  deriving DecidableEq, Fintype, Repr

/-- The immediate supersorts of a sort. Each filler-gap clause other than the topicalized clause
and each aux-initial clause has two, a headed construct and a clause type. -/
def Srt.parents : Srt → List Srt
  | .top => []
  | .cat | .vform | .boolean | .semType | .list | .idx | .sign | .construct => [.top]
  | .verbal | .nonverbal => [.cat]
  | .verb | .comp => [.verbal]
  | .nominal | .adj | .adv => [.nonverbal]
  | .noun | .prep => [.nominal]
  | .presentPart | .perfectPart | .passivePart | .core | .base | .gerund => [.vform]
  | .fin | .inf => [.core]
  | .plus | .minus => [.boolean]
  | .austinean | .question | .fact | .modifier => [.semType]
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
  | .finWhRelCl | .infWhRelCl => [.whRelCl]
  | .polarIntCl => [.auxInitialCxt, .interrogativeCl]
  | .auxInitialExclCl => [.auxInitialCxt, .exclamativeCl]

/-- The length of the longest chain from a sort up to `top`. -/
def Srt.rank : Srt → ℕ
  | .top => 0
  | .cat | .vform | .boolean | .semType | .list | .idx | .sign | .construct => 1
  | .verbal | .nonverbal | .presentPart | .perfectPart | .passivePart | .core | .base | .gerund
  | .plus | .minus | .austinean | .question | .fact | .modifier | .elist | .nelist | .overtExpr
  | .covertExpr | .phrasalCxt => 2
  | .verb | .comp | .nominal | .adj | .adv | .fin | .inf | .gap | .headedCxt | .clause
  | .coordCxt => 3
  | .noun | .prep | .fillerHeadCxt | .auxInitialCxt | .coreCl | .relativeCl => 4
  | .declarativeCl | .interrogativeCl | .exclamativeCl | .topCl | .whRelCl => 5
  | .whExclCl | .nsWhIntCl | .finWhRelCl | .infWhRelCl | .theCl | .polarIntCl
  | .auxInitialExclCl => 6

theorem Srt.rank_lt_of_mem_parents : ∀ σ : Srt, ∀ τ ∈ σ.parents, τ.rank < σ.rank := by
  decide +kernel

instance : PartialOrder Srt :=
  partialOrderOfCovers (fun σ τ : Srt ↦ τ ∈ σ.parents) Srt.rank Srt.rank_lt_of_mem_parents

instance : DecidableLE Srt :=
  decidableLEOfRank (covers := fun σ τ : Srt ↦ τ ∈ σ.parents) Srt.parents Srt.rank
    (fun _ _ ↦ Iff.rfl) Srt.rank_lt_of_mem_parents

/-! ### Attributes and the signature -/

/-- The attributes. A construct has a mother and daughters. A sign has a category, a `GAP` list,
a semantic type and an index. A verbal category has a verb form and is independent or not, and a
verb is inverted or not. A nonempty list has a first element and a rest. -/
inductive Attr
  | MTR | HDDTR | FILLERDTR | CONJ1 | CONJ2 | CAT | VFORM | IC | INV | GAP | SEM | INDEX | FIRST
  | REST
  deriving DecidableEq, Fintype, Repr

/-- The sorts that introduce each attribute, with its value sort there. The mother of a phrasal
construct and its daughters are overt, and a list contains signs. -/
def Attr.decl : Attr → List (Srt × Srt)
  | .MTR => [(.phrasalCxt, .overtExpr)]
  | .HDDTR => [(.headedCxt, .overtExpr)]
  | .FILLERDTR => [(.fillerHeadCxt, .overtExpr)]
  | .CONJ1 | .CONJ2 => [(.coordCxt, .overtExpr)]
  | .CAT => [(.sign, .cat)]
  | .VFORM => [(.verbal, .vform)]
  | .IC => [(.verbal, .boolean)]
  | .INV => [(.verb, .boolean)]
  | .GAP => [(.sign, .list)]
  | .SEM => [(.sign, .semType)]
  | .INDEX => [(.sign, .idx)]
  | .FIRST => [(.nelist, .sign)]
  | .REST => [(.nelist, .list)]

/-- The one relation symbol is list membership. -/
inductive Rel | member
  deriving DecidableEq, Fintype, Repr

/-- The signature of the fragment. -/
@[reducible] def sig : Signature Srt := .ofDecl Attr Rel (fun _ ↦ 2) Attr.decl (by decide +kernel)

/-- A nonsubject wh-interrogative construct inherits its mother from the phrasal construct and
its filler daughter from the filler-head construct, a coordinate construct has no filler
daughter, and a complementizer is not inverted or uninverted. -/
example : sig.approp .nsWhIntCl .MTR = some .overtExpr ∧
    sig.approp .nsWhIntCl .FILLERDTR = some .overtExpr ∧
    sig.approp .coordCxt .FILLERDTR = none ∧ sig.approp .comp .INV = none := by decide +kernel

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

/-- The core clause construction of [sag-2010]: the mother of a core clause is finite or
infinitival. -/
def corePrinciple : Constraint sig :=
  ⟨.coreCl, .sortAssign (.path [.MTR, .CAT, .VFORM]) .core⟩

/-- The mother of a declarative clause has an austinean semantic type. -/
def declarativePrinciple : Constraint sig :=
  ⟨.declarativeCl, .sortAssign (.path [.MTR, .SEM]) .austinean⟩

/-- The mother of an interrogative clause denotes a question. -/
def interrogativePrinciple : Constraint sig :=
  ⟨.interrogativeCl, .sortAssign (.path [.MTR, .SEM]) .question⟩

/-- The mother of an exclamative clause denotes a fact. -/
def exclamativePrinciple : Constraint sig :=
  ⟨.exclamativeCl, .sortAssign (.path [.MTR, .SEM]) .fact⟩

/-- The relative construction ([sag-2010] (91)): the mother of a relative clause is neither
inverted nor independent. -/
def relativePrinciple : Constraint sig :=
  ⟨.relativeCl, .and (.sortAssign (.path [.MTR, .CAT, .INV]) .minus)
    (.sortAssign (.path [.MTR, .CAT, .IC]) .minus)⟩

/-- The topicalization construction ([sag-2010] (61)). The filler daughter is nonverbal. The head
daughter is an uninverted, independent, finite projection of a verb, which excludes the
complementizer-headed clause that a the-clause allows, and it has exactly one gap. The mother is
austinean. -/
def topPrinciple : Constraint sig :=
  ⟨.topCl, .and (.sortAssign (.path [.FILLERDTR, .CAT]) .nonverbal)
    (.and (.sortAssign (.path [.HDDTR, .CAT]) .verb)
      (.and (.sortAssign (.path [.HDDTR, .CAT, .INV]) .minus)
        (.and (.sortAssign (.path [.HDDTR, .CAT, .IC]) .plus)
          (.and (.sortAssign (.path [.HDDTR, .CAT, .VFORM]) .fin)
            (.and (.sortAssign (.path [.HDDTR, .GAP, .REST]) .elist)
              (.sortAssign (.path [.MTR, .SEM]) .austinean))))))⟩

/-- The wh-exclamative construction ([sag-2010] (70)). The filler daughter is nonverbal, and the
head daughter is uninverted and finite and has exactly one gap. -/
def whExclPrinciple : Constraint sig :=
  ⟨.whExclCl, .and (.sortAssign (.path [.FILLERDTR, .CAT]) .nonverbal)
    (.and (.sortAssign (.path [.HDDTR, .CAT, .INV]) .minus)
      (.and (.sortAssign (.path [.HDDTR, .CAT, .VFORM]) .fin)
        (.sortAssign (.path [.HDDTR, .GAP, .REST]) .elist)))⟩

/-- The nonsubject wh-interrogative construction ([sag-2010] (80)). The filler daughter is
nonverbal, and the head daughter is inverted exactly when it is independent. -/
def nsWhIntPrinciple : Constraint sig :=
  ⟨.nsWhIntCl, .and (.sortAssign (.path [.FILLERDTR, .CAT]) .nonverbal)
    (.pathEq (.path [.HDDTR, .CAT, .INV]) (.path [.HDDTR, .CAT, .IC]))⟩

/-- The wh-relative construction ([sag-2010] (90)) gives the mother the semantic type of a
modifier. -/
def whRelPrinciple : Constraint sig :=
  ⟨.whRelCl, .sortAssign (.path [.MTR, .SEM]) .modifier⟩

/-- The finite wh-relative construction ([sag-2010] (92)). The mother is finite and the filler
daughter nominal, a noun phrase or a prepositional phrase. -/
def finWhRelPrinciple : Constraint sig :=
  ⟨.finWhRelCl, .and (.sortAssign (.path [.MTR, .CAT, .VFORM]) .fin)
    (.sortAssign (.path [.FILLERDTR, .CAT]) .nominal)⟩

/-- The infinitival wh-relative construction of [sag-2010]. The filler daughter is a
prepositional phrase and the head daughter is infinitival. -/
def infWhRelPrinciple : Constraint sig :=
  ⟨.infWhRelCl, .and (.sortAssign (.path [.FILLERDTR, .CAT]) .prep)
    (.sortAssign (.path [.HDDTR, .CAT, .VFORM]) .inf)⟩

/-- The the-clause construction ([sag-2010] (108)). The filler daughter is nonverbal, and the
head daughter is finite and has exactly one gap. -/
def thePrinciple : Constraint sig :=
  ⟨.theCl, .and (.sortAssign (.path [.FILLERDTR, .CAT]) .nonverbal)
    (.and (.sortAssign (.path [.HDDTR, .CAT, .VFORM]) .fin)
      (.sortAssign (.path [.HDDTR, .GAP, .REST]) .elist))⟩

/-- The constructions of the fragment. -/
def constraints : List (Constraint sig) :=
  [headedPrinciple, fillerHeadPrinciple, corePrinciple, declarativePrinciple,
    interrogativePrinciple, exclamativePrinciple, relativePrinciple, topPrinciple,
    whExclPrinciple, nsWhIntPrinciple, whRelPrinciple, finWhRelPrinciple, infWhRelPrinciple,
    thePrinciple]

/-- The grammar of the fragment. -/
def grammar : Grammar sig := constraints.map Constraint.toDesc

theorem freeVars_grammar : ∀ d ∈ grammar, d.freeVars = ∅ := by decide

/-- The signature admits the paths of the filler-head construction from the sort it constrains,
and it admits no filler daughter in a coordinate construct. -/
example : sig.Admits .fillerHeadCxt [.HDDTR, .GAP, .FIRST, .INDEX] .idx ∧
    sig.Admits .fillerHeadCxt [.HDDTR, .GAP, .REST] .elist ∧
    ¬ ∃ ρ, sig.Admits .coordCxt [.FILLERDTR, .CAT] ρ := by decide +kernel

/-! ### Inheritance -/

theorem map_sort_inherited_fillerGap :
    (Constraint.inherited constraints .topCl).map (·.sort) =
        [.headedCxt, .fillerHeadCxt, .topCl] ∧
      (Constraint.inherited constraints .whExclCl).map (·.sort) =
        [.headedCxt, .fillerHeadCxt, .coreCl, .exclamativeCl, .whExclCl] ∧
      (Constraint.inherited constraints .nsWhIntCl).map (·.sort) =
        [.headedCxt, .fillerHeadCxt, .coreCl, .interrogativeCl, .nsWhIntCl] ∧
      (Constraint.inherited constraints .finWhRelCl).map (·.sort) =
        [.headedCxt, .fillerHeadCxt, .relativeCl, .whRelCl, .finWhRelCl] ∧
      (Constraint.inherited constraints .infWhRelCl).map (·.sort) =
        [.headedCxt, .fillerHeadCxt, .relativeCl, .whRelCl, .infWhRelCl] ∧
      (Constraint.inherited constraints .theCl).map (·.sort) =
        [.headedCxt, .fillerHeadCxt, .coreCl, .declarativeCl, .theCl] := by
  decide +kernel

variable {U : Type*} {I : Interpretation sig U} {g : ℕ → U} {u : U}

theorem satisfies_body (hI : I.Models grammar) {c : Constraint sig} (hc : c ∈ constraints)
    (hu : I.S u ≤ c.sort) : I.Satisfies (fun _ ↦ u) u c.body :=
  hI.satisfies_body (List.mem_map_of_mem hc) hu

theorem forall_satisfies_grammar_iff_of_nsWhIntCl (hu : I.S u = .nsWhIntCl) :
    (∀ d ∈ grammar, I.Satisfies g u d) ↔
      ∀ c ∈ [headedPrinciple, fillerHeadPrinciple, corePrinciple, interrogativePrinciple,
        nsWhIntPrinciple], I.Satisfies g u c.body := by
  rw [grammar, Interpretation.forall_satisfies_map_toDesc_iff, hu]
  rfl

theorem satisfies_mtrGap_iff (hI : I.Models grammar) (hu : I.S u ≤ .fillerHeadCxt) (σ : Srt) :
    I.Satisfies (fun _ ↦ u) u (.sortAssign (.path [.MTR, .GAP]) σ) ↔
      I.Satisfies (fun _ ↦ u) u (.sortAssign (.path [.HDDTR, .GAP, .REST]) σ) := by
  obtain ⟨-, -, -, -, v, hv, hv'⟩ :=
    satisfies_body hI (c := fillerHeadPrinciple) (by simp [constraints]) hu
  simp only [Interpretation.satisfies_sortAssign]
  constructor <;> rintro ⟨w, hw, hle⟩
  · obtain rfl : w = v := Option.mem_unique hw hv
    exact ⟨w, hv', hle⟩
  · obtain rfl : w = v := Option.mem_unique hw hv'
    exact ⟨w, hv, hle⟩

theorem satisfies_hdCat_iff (hI : I.Models grammar) (hu : I.S u ≤ .headedCxt) (p : Path sig)
    (σ : Srt) :
    I.Satisfies (fun _ ↦ u) u (.sortAssign (.path (.MTR :: .CAT :: p)) σ) ↔
      I.Satisfies (fun _ ↦ u) u (.sortAssign (.path (.HDDTR :: .CAT :: p)) σ) := by
  obtain ⟨v, hv, hv'⟩ := satisfies_body hI (c := headedPrinciple) (by simp [constraints]) hu
  simp only [Interpretation.satisfies_sortAssign]
  rw [show (Attr.MTR :: .CAT :: p : Path sig) = [.MTR, .CAT] ++ p from rfl,
    show (Attr.HDDTR :: .CAT :: p : Path sig) = [.HDDTR, .CAT] ++ p from rfl,
    Interpretation.termDenot_path_append, Interpretation.termDenot_path_append,
    Option.mem_def.1 hv, Option.mem_def.1 hv']

theorem satisfies_le_of_mem_termDenot (hI : I.IsWellTyped) {p : Path sig} {α : Attr} {σ : Srt}
    (hσ : ∀ d ∈ Attr.decl α, d.1 ≤ σ) {v : U}
    (hv : v ∈ I.termDenot g (.path (p ++ [α])) u) :
    I.Satisfies g u (.sortAssign (.path p) σ) := by
  rw [Interpretation.termDenot_path_append, Option.mem_def, Option.bind_eq_some_iff] at hv
  obtain ⟨w, hw, hα⟩ := hv
  obtain ⟨τ, hτ, -⟩ := hI α w v (by simpa [Term.path, Interpretation.termDenot] using hα)
  obtain ⟨d, hd, hle, -⟩ := exists_mem_decl_of_appropOfDecl_eq_some _ hτ
  exact ⟨w, hw, hle.trans (hσ d hd)⟩

theorem not_le_covertExpr (hI : I.IsWellTyped) {α : sig.Attr}
    (hα : α ∈ [.MTR, .HDDTR, .FILLERDTR, .CONJ1, .CONJ2]) {v : U} (hv : I.A α u = some v) :
    ¬ I.S v ≤ .covertExpr := by
  obtain ⟨τ, hτ, hle⟩ := hI α u v hv
  obtain ⟨d, hd, -, rfl⟩ := exists_mem_decl_of_appropOfDecl_eq_some _ hτ
  rw [(by decide : ∀ α ∈ ([.MTR, .HDDTR, .FILLERDTR, .CONJ1, .CONJ2] : List Attr),
    ∀ d ∈ Attr.decl α, d.2 = .overtExpr) α hα d hd] at hle
  exact (by decide +kernel : ∀ σ : Srt, σ ≤ .overtExpr → ¬ σ ≤ .covertExpr) _ hle

/-! ### The `GAP` list as a set

The filler-head construction discharges the first sign on the `GAP` list. The relation
`member`, which `memberDef` defines, lets a principle speak of any element instead. -/

/-- The entity `x` is an element of the list `l` when some cell that `REST` reaches from `l` has
`x` as its first element. -/
def ListMem (I : Interpretation sig U) (x l : U) : Prop :=
  ∃ c, Relation.ReflTransGen (fun a b ↦ I.A .REST a = some b) l c ∧ I.A .FIRST c = some x

instance [Fintype U] [DecidableEq U] (x l : U) : Decidable (ListMem I x l) := by
  unfold ListMem; infer_instance

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

private theorem le_nelist_of_A {α : sig.Attr} (hI : I.IsWellTyped) (hα : α = .FIRST ∨ α = .REST)
    {l v : U} (h : I.A α l = some v) : I.S l ≤ .nelist := by
  obtain ⟨τ, hτ, -⟩ := hI α l v h
  obtain ⟨d, hd, hle, -⟩ := exists_mem_decl_of_appropOfDecl_eq_some _ hτ
  rwa [(by decide : ∀ α ∈ ([.FIRST, .REST] : List Attr), ∀ d ∈ Attr.decl α, d.1 = .nelist) α
    (by rcases hα with rfl | rfl <;> simp) d hd] at hle

private theorem and_or_listMem_iff (hI : I.IsWellTyped) {x l : U} :
    (I.S l ≤ .nelist ∧ (I.A .FIRST l = some x ∨ ∃ y, I.A .REST l = some y ∧ ListMem I x y)) ↔
      ListMem I x l :=
  ⟨fun h ↦ listMem_iff.2 h.2, fun h ↦ ⟨(listMem_iff.1 h).elim (le_nelist_of_A hI (.inl rfl))
    fun ⟨_, hy, _⟩ ↦ le_nelist_of_A hI (.inr rfl) hy, listMem_iff.1 h⟩⟩

theorem models_memberDef_of_forall (hI : I.IsWellTyped)
    (h : ∀ u x l, I.IsComponentOf u x → I.IsComponentOf u l →
      (I.R .member ![x, l] ↔ ListMem I x l)) : I.Models [memberDef] := by
  intro u d hd
  rw [List.mem_singleton.1 hd]
  refine satisfies_memberDef_iff.2 fun x hx l hl ↦ ?_
  rw [h u x l hx hl, ← and_or_listMem_iff hI]
  exact and_congr_right fun _ ↦ or_congr_right <| exists_congr fun y ↦
    and_congr_right fun hy ↦ (h u x y hx (hl.tail ⟨_, hy⟩)).symm

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

end HPSG.Construction
