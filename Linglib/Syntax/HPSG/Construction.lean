/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.RSRL.Semantics
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.FinCases

/-!
# The construct hierarchy of Sign-Based Construction Grammar in RSRL

In Sign-Based Construction Grammar a *construct* is a mother sign with its daughter signs, and a
*construction* is a constraint on the constructs of one sort. This file states in RSRL the part
of the grammar with which Sag analyses the English filler-gap clauses, such as *My bagels, she
likes*.

Construct sorts are classified by how they are headed and by the kind of clause they form, and a
sort below one of each inherits the constraints on both. The *filler-head* construction
identifies the filler daughter with the first sign on the head daughter's `GAP` list and passes
the rest of the list to the mother (`HPSG.Construction.sortAt_mtr_gap_iff`). The principle
`HPSG.Construction.memberDef` defines the relation symbol `member` as list membership.

## Implementation notes

As in Sag's grammars, a `GAP` list contains signs, and a word leaves a covert sign of sort `gap`
on it for an argument that it does not realize. Daughters are attributes named by their role,
not members of a `DTRS` list. The signature has only the features that the constructions here
mention; `WH`, `REL`, `VAL`, `SELECT`, `GRAM` and `STORE` are left out, and the semantic type of
the mother stands in for its meaning.

The subject-predicate, predicational head-complement and aux-initial constructions are in
`Studies/SagEtAl2020`, the coordinate construction in `Studies/SagWasowBender2003`, and the
worked constructs in `Studies/Sag2010`.

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
  | subjHeadCxt | predHdCompCxt
  -- clause types
  | coreCl | relativeCl | declarativeCl | interrogativeCl | exclamativeCl
  -- clauses that are headed constructs
  | topCl | whExclCl | nsWhIntCl | whRelCl | finWhRelCl | infWhRelCl | theCl | polarIntCl
  | auxInitialExclCl | subjPredCl
  deriving DecidableEq, Fintype, Repr

/-- The immediate supersorts of a sort. Each filler-gap clause other than the topicalized clause,
each aux-initial clause and the subject-predicate clause has two, a headed construct and a clause
type. -/
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
  | .fillerHeadCxt | .auxInitialCxt | .subjHeadCxt | .predHdCompCxt => [.headedCxt]
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
  | .subjPredCl => [.subjHeadCxt, .declarativeCl]

/-- The length of the longest chain from a sort up to `top`. -/
def Srt.rank : Srt → ℕ
  | .top => 0
  | .cat | .vform | .boolean | .semType | .list | .idx | .sign | .construct => 1
  | .verbal | .nonverbal | .presentPart | .perfectPart | .passivePart | .core | .base | .gerund
  | .plus | .minus | .austinean | .question | .fact | .modifier | .elist | .nelist | .overtExpr
  | .covertExpr | .phrasalCxt => 2
  | .verb | .comp | .nominal | .adj | .adv | .fin | .inf | .gap | .headedCxt | .clause
  | .coordCxt => 3
  | .noun | .prep | .fillerHeadCxt | .auxInitialCxt | .subjHeadCxt | .predHdCompCxt | .coreCl
  | .relativeCl => 4
  | .declarativeCl | .interrogativeCl | .exclamativeCl | .topCl | .whRelCl => 5
  | .whExclCl | .nsWhIntCl | .finWhRelCl | .infWhRelCl | .theCl | .polarIntCl
  | .auxInitialExclCl | .subjPredCl => 6

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
verb is inverted or not and has a positive or a negative value for `AUX`. A nonempty list has a
first element and a rest. -/
inductive Attr
  | MTR | HDDTR | FILLERDTR | CONJ1 | CONJ2 | CAT | VFORM | IC | INV | AUX | GAP | SEM | INDEX
  | FIRST | REST
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
  | .INV | .AUX => [(.verb, .boolean)]
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

instance {U : Type*} (ρ : sig.Rel) : DecidablePred (· ∈ @noRel U ρ) := fun _ ↦ instDecidableFalse

/-! ### Constructions -/

/-- The headed construction of [sag-2010]: the mother of a headed construct has the category of
its head daughter. -/
def headedPrinciple : Constraint sig where
  sort := .headedCxt
  atoms := [.eq [.MTR, .CAT] [.HDDTR, .CAT]]

/-- The filler-head construction ([sag-2010] (58), [sag-2012] (141)). The head daughter is
verbal. The filler daughter shares its category, its `GAP` list and its index with the first
sign on the head daughter's `GAP` list, and the mother's `GAP` list is the rest of the head
daughter's. -/
def fillerHeadPrinciple : Constraint sig where
  sort := .fillerHeadCxt
  atoms :=
    [.sort [.HDDTR, .CAT] .verbal,
      .eq [.FILLERDTR, .CAT] [.HDDTR, .GAP, .FIRST, .CAT],
      .eq [.FILLERDTR, .GAP] [.HDDTR, .GAP, .FIRST, .GAP],
      .eq [.FILLERDTR, .INDEX] [.HDDTR, .GAP, .FIRST, .INDEX],
      .eq [.MTR, .GAP] [.HDDTR, .GAP, .REST]]

/-- The core clause construction of [sag-2010]: the mother of a core clause is finite or
infinitival. -/
def corePrinciple : Constraint sig where
  sort := .coreCl
  atoms := [.sort [.MTR, .CAT, .VFORM] .core]

/-- The mother of a declarative clause has an austinean semantic type. -/
def declarativePrinciple : Constraint sig where
  sort := .declarativeCl
  atoms := [.sort [.MTR, .SEM] .austinean]

/-- The mother of an interrogative clause denotes a question. -/
def interrogativePrinciple : Constraint sig where
  sort := .interrogativeCl
  atoms := [.sort [.MTR, .SEM] .question]

/-- The mother of an exclamative clause denotes a fact. -/
def exclamativePrinciple : Constraint sig where
  sort := .exclamativeCl
  atoms := [.sort [.MTR, .SEM] .fact]

/-- The relative construction ([sag-2010] (91)): the mother of a relative clause is neither
inverted nor independent. -/
def relativePrinciple : Constraint sig where
  sort := .relativeCl
  atoms := [.sort [.MTR, .CAT, .INV] .minus, .sort [.MTR, .CAT, .IC] .minus]

/-- The topicalization construction ([sag-2010] (61)). The filler daughter is nonverbal. The head
daughter is an uninverted, independent, finite projection of a verb, which excludes the
complementizer-headed clause that a the-clause allows, and it has exactly one gap. The mother is
austinean. -/
def topPrinciple : Constraint sig where
  sort := .topCl
  atoms :=
    [.sort [.FILLERDTR, .CAT] .nonverbal,
      .sort [.HDDTR, .CAT] .verb,
      .sort [.HDDTR, .CAT, .INV] .minus,
      .sort [.HDDTR, .CAT, .IC] .plus,
      .sort [.HDDTR, .CAT, .VFORM] .fin,
      .sort [.HDDTR, .GAP, .REST] .elist,
      .sort [.MTR, .SEM] .austinean]

/-- The wh-exclamative construction ([sag-2010] (70)). The filler daughter is nonverbal, and the
head daughter is uninverted and finite and has exactly one gap. -/
def whExclPrinciple : Constraint sig where
  sort := .whExclCl
  atoms :=
    [.sort [.FILLERDTR, .CAT] .nonverbal,
      .sort [.HDDTR, .CAT, .INV] .minus,
      .sort [.HDDTR, .CAT, .VFORM] .fin,
      .sort [.HDDTR, .GAP, .REST] .elist]

/-- The nonsubject wh-interrogative construction ([sag-2010] (80)). The filler daughter is
nonverbal, and the head daughter is inverted exactly when it is independent. -/
def nsWhIntPrinciple : Constraint sig where
  sort := .nsWhIntCl
  atoms := [.sort [.FILLERDTR, .CAT] .nonverbal, .eq [.HDDTR, .CAT, .INV] [.HDDTR, .CAT, .IC]]

/-- The wh-relative construction ([sag-2010] (90)) gives the mother the semantic type of a
modifier. -/
def whRelPrinciple : Constraint sig where
  sort := .whRelCl
  atoms := [.sort [.MTR, .SEM] .modifier]

/-- The finite wh-relative construction ([sag-2010] (92)). The mother is finite and the filler
daughter nominal, a noun phrase or a prepositional phrase. -/
def finWhRelPrinciple : Constraint sig where
  sort := .finWhRelCl
  atoms := [.sort [.MTR, .CAT, .VFORM] .fin, .sort [.FILLERDTR, .CAT] .nominal]

/-- The infinitival wh-relative construction of [sag-2010]. The filler daughter is a
prepositional phrase and the head daughter is infinitival. -/
def infWhRelPrinciple : Constraint sig where
  sort := .infWhRelCl
  atoms := [.sort [.FILLERDTR, .CAT] .prep, .sort [.HDDTR, .CAT, .VFORM] .inf]

/-- The the-clause construction ([sag-2010] (108)). The filler daughter is nonverbal, and the
head daughter is finite and has exactly one gap. -/
def thePrinciple : Constraint sig where
  sort := .theCl
  atoms :=
    [.sort [.FILLERDTR, .CAT] .nonverbal,
      .sort [.HDDTR, .CAT, .VFORM] .fin,
      .sort [.HDDTR, .GAP, .REST] .elist]

/-- The constructions of the fragment. -/
def constraints : List (Constraint sig) :=
  [headedPrinciple, fillerHeadPrinciple, corePrinciple, declarativePrinciple,
    interrogativePrinciple, exclamativePrinciple, relativePrinciple, topPrinciple,
    whExclPrinciple, nsWhIntPrinciple, whRelPrinciple, finWhRelPrinciple, infWhRelPrinciple,
    thePrinciple]

/-- The grammar of the fragment. -/
abbrev grammar : Grammar sig := .ofConstraints constraints

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

/-- An entity of the nonsubject wh-interrogative sort satisfies the grammar exactly when the
atoms of the headed, filler-head, core clause, interrogative and nonsubject wh-interrogative
constructions hold of it. Only the last is stated on its sort. -/
theorem forall_satisfies_grammar_iff_of_nsWhIntCl (hu : I.S u = .nsWhIntCl) :
    (∀ d ∈ grammar, I.Satisfies g u d) ↔
      ∀ c ∈ [headedPrinciple, fillerHeadPrinciple, corePrinciple, interrogativePrinciple,
        nsWhIntPrinciple], ∀ a ∈ c.atoms, a.Holds I u := by
  rw [Interpretation.forall_satisfies_ofConstraints_iff, hu]
  rfl

/-- In a model of the grammar, the mother of a filler-head construct has a `GAP` list of sort
`σ` exactly when the rest of its head daughter's list does, since the filler discharges the
first gap and the rest passes up. The mother's list is therefore empty exactly when the head
daughter has one gap. -/
theorem sortAt_mtr_gap_iff (hI : I.Models grammar) (hu : I.S u ≤ .fillerHeadCxt) (σ : Srt) :
    I.SortAt u [.MTR, .GAP] σ ↔ I.SortAt u [.HDDTR, .GAP, .REST] σ :=
  (hI.pathEq fillerHeadPrinciple hu).sortAt_iff

/-- In a model of the grammar, the mother and the head daughter of a headed construct share
their category, so a feature of the mother's category has the same value on the head's. -/
theorem sortAt_mtr_cat_iff (hI : I.Models grammar) (hu : I.S u ≤ .headedCxt) (p : Path sig)
    (σ : Srt) : I.SortAt u (.MTR :: .CAT :: p) σ ↔ I.SortAt u (.HDDTR :: .CAT :: p) σ :=
  (hI.pathEq headedPrinciple hu (p := [.MTR, .CAT]) (q := [.HDDTR, .CAT])).sortAt_append_iff p

/-- In a well-typed interpretation, a path that an attribute continues leads to an entity of a
sort that introduces the attribute. -/
theorem sortAt_of_sortAt_concat (hI : I.IsWellTyped) {p : Path sig} {α : Attr} {σ τ : Srt}
    (hσ : ∀ d ∈ Attr.decl α, d.1 ≤ σ) (h : I.SortAt u (p ++ [α]) τ) : I.SortAt u p σ := by
  obtain ⟨w, hw, v, hv, -⟩ := Interpretation.sortAt_append.1 h
  obtain ⟨ρ, hρ, -⟩ := hI α w v (by simpa [Interpretation.eval_cons] using hv)
  obtain ⟨d, hd, hle, -⟩ := exists_mem_decl_of_appropOfDecl_eq_some _ hρ
  exact ⟨w, hw, hle.trans (hσ d hd)⟩

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
def memberDef : Description sig where
  toFormula := .all 0 (.all 1 (.iff (.rel .member ![0, 1])
    (.and (.sortAssign (.var 1) .nelist)
      (.or (.pathEq (.var 0) (.feat (.var 1) .FIRST))
        (.ex 2 (.and (.pathEq (.var 2) (.feat (.var 1) .REST)) (.rel .member ![0, 2])))))))

theorem satisfies_memberDef_iff : I.Satisfies g u memberDef ↔
    ∀ x, I.IsComponentOf u x → ∀ l, I.IsComponentOf u l →
      (![x, l] ∈ I.R .member ↔ I.S l ≤ .nelist ∧
        (I.A .FIRST l = some x ∨ ∃ y, I.A .REST l = some y ∧ ![x, y] ∈ I.R .member)) := by
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
      (![x, l] ∈ I.R .member ↔ ListMem I x l)) : I.Models {memberDef} := by
  rintro d rfl g u
  refine satisfies_memberDef_iff.2 fun x hx l hl ↦ ?_
  rw [h u x l hx hl, ← and_or_listMem_iff hI]
  exact and_congr_right fun _ ↦ or_congr_right <| exists_congr fun y ↦
    and_congr_right fun hy ↦ (h u x y hx (hl.tail ⟨_, hy⟩)).symm

/-- On lists without cycles the principle `memberDef` defines list membership. A well-typed
interpretation models it exactly when `member` holds of two components of an entity just when
the first is an element of the second. -/
theorem models_memberDef_iff (hI : I.IsWellTyped)
    (hwf : WellFounded fun b a ↦ I.A .REST a = some b) :
    I.Models {memberDef} ↔ ∀ u x l, I.IsComponentOf u x → I.IsComponentOf u l →
      (![x, l] ∈ I.R .member ↔ ListMem I x l) := by
  refine ⟨fun hM u x l hx hl ↦ ?_, models_memberDef_of_forall hI⟩
  have hu := satisfies_memberDef_iff.1 (hM _ rfl (fun _ ↦ u) u)
  induction l using hwf.induction with
  | h l ih =>
    rw [hu x hx l hl, ← and_or_listMem_iff hI]
    exact and_congr_right fun _ ↦ or_congr_right <| exists_congr fun y ↦
      and_congr_right fun hy ↦ ih y hy (hl.tail ⟨_, hy⟩)

end HPSG.Construction
