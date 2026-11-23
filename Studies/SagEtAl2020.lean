module

public import Linglib.Syntax.HPSG.Construction
public import Linglib.Syntax.HPSG.RSRL.Satisfiability
public import Linglib.Core.Order.BoundedComplete
public import Linglib.Data.Examples.SagEtAl2020
public import Studies.Sag2010

/-!
# Sag et al. (2020): Lessons from the English Auxiliary System

The category of a verb has the features `AUX` and `INV`, each with a positive or a negative
value, and a verb form. The listeme of a verb specifies some of these features and leaves the
others open: a lexical verb is `[AUX −]` and `[INV −]`, auxiliary *do* is `[AUX +]`, *better* is
`[INV −]`, deontic *shall* is `[INV +]`, and a modal such as *can* specifies neither. A
construction specifies the features of its head daughter in the same way. The head of a
subject-head construct and of a predicational head-complement construct is `[AUX −]` and
`[INV −]`, and the head of an aux-initial construct is `[INV +]`.

We define a *specification* as a sort for each of the three features, an open feature having the
sort of all its values, and state the three constructions on the construct hierarchy of
`Linglib/Syntax/HPSG/Construction.lean`. A specified category *can head* a construct sort when
the description of a construct of that sort whose head daughter satisfies the specification is
satisfiable over the grammar: some well-typed model has such a construct. The main result,
`SagEtAl2020.canHead_iff`, says that it can exactly when it is compatible with the specification
of the construction, that is, when they unify: for each feature the two sorts have a common
subsort (`SagEtAl2020.Specification.compat_iff`). A subject-predicate clause, a polar
interrogative and an inverted exclamative inherit the specification of their headed construction
and narrow the verb form (`SagEtAl2020.canHead_clause_iff`). An example is acceptable exactly when a specification of its
verb can head a clause of its type (`SagEtAl2020.judgments`), apart from two examples that turn
on stress and on `GRAM` (`SagEtAl2020.judgments_unaccounted`), and a sense of *shall* is
available exactly where the listeme with that sense can head the clause
(`SagEtAl2020.shall_readings`).

The mother of an aux-initial construct has the category of its head daughter and so is inverted.
It is therefore not the head daughter of a construct whose head is uninverted, among them the
topicalized clauses, wh-exclamatives and wh-relatives of [sag-2010]
(`SagEtAl2020.mtr_ne_hdDtr`), and a nonsubject wh-interrogative that it heads is an independent
clause (`SagEtAl2020.sortAt_hdDtr_ic`, with the worked construct
`SagEtAl2020.whConstruct`). In a worked polar interrogative or inverted exclamative the mother
is an independent clause that denotes a question or a fact (`SagEtAl2020.models_clause_iff`).

## Implementation notes

The valence conditions of the constructions are not stated: that the head daughter of an
aux-initial or a head-complement construct is a word whose valents are its sisters, and that the
mother of an aux-initial construct is saturated. The signature has no `VAL`, no `GRAM` and no
distinction of words from phrases, so the verb form that an auxiliary selects and the complement
of *do* are not constrained, and a listeme is its specification of the head features.

The subject-predicate construction is factored as in the paper's summary of the grammar: the
subject-head construction requires a head that is `[AUX −]` and `[INV −]`, and the
subject-predicate clause a finite one. The aux-initial construction requires `[INV +]` of its
head and nothing of `AUX`, so a lexical verb is excluded from it by its `[INV −]`. The
predicational head-complement construction requires `[AUX −]`, so auxiliary *do* heads no
head-complement construct here.

As in the paper the hierarchy of constructs is partial, and the models over which
`HPSG.RSRL.Grammar.IsSatisfiable` ranges are well-typed and not sort-resolved. A construct may then
bear the sort of the aux-initial construction itself, as the head daughter of a wh-interrogative
does, and `SagEtAl2020.canHead_iff` is about those; the three clause types of
`SagEtAl2020.canHead_clause_iff` are maximal sorts. The semantic type of a subject-predicate
clause is that of the declarative clause of [sag-2010].

## TODO

* The lexical constructions of the paper, negation, contraction, ellipsis and rebuttal. Rebuttal
  and ellipsis make an `[AUX +]` verb available to the subject-predicate clause, which is what
  licenses stressed *do*.
* The conditional, blessing and negative imperative aux-initial clauses.

## References

* [sag-etal-2020]
* [sag-2010]
-/

@[expose] public section

namespace SagEtAl2020

open HPSG.RSRL HPSG.Construction

/-! ### Specifications of the head features -/

/-- The features of a verbal category that the constructions constrain. -/
inductive HeadFeature where
  | aux
  | inv
  | vform
  deriving DecidableEq, Fintype, Repr

/-- The attribute of a head feature. -/
def HeadFeature.attr : HeadFeature → Attr
  | .aux => .AUX
  | .inv => .INV
  | .vform => .VFORM

/-- A specification gives a sort to each head feature of a verbal category. A feature that it
leaves open has the sort of all its values, `boolean` or `vform`. -/
abbrev Specification := HeadFeature → Srt

namespace Specification

/-- The specification with the given sorts, each feature open unless a sort is given. -/
def of (aux inv : Srt := .boolean) (vf : Srt := .vform) : Specification
  | .aux => aux
  | .inv => inv
  | .vform => vf

/-- The atoms that say of the sign at the end of the path `p` that each head feature of its
category has a value of the specified sort. -/
def atoms (ℓ : Specification) (p : Path sig) : List (PathAtom sig) :=
  [HeadFeature.aux, .inv, .vform].map fun f ↦ .sort (p ++ [.CAT, f.attr]) (ℓ f)

variable {U : Type*} {I : Interpretation sig U} {u : U}

theorem forall_mem_atoms {ℓ : Specification} {p : Path sig} :
    (∀ a ∈ ℓ.atoms p, a.Holds I u) ↔
      ∀ f : HeadFeature, I.SortAt u (p ++ [.CAT, f.attr]) (ℓ f) := by
  rw [atoms, List.forall_mem_map]
  exact ⟨fun h f ↦ h f (by cases f <;> simp), fun h f _ ↦ h f⟩

-- compatibility in the order in which the more specific sort is the greater
theorem compat_iff {ℓ r : Specification} :
    Compat (α := HeadFeature → Srtᵒᵈ) ℓ r ↔ ∀ f, ∃ τ, τ ≤ ℓ f ∧ τ ≤ r f :=
  (compat_pi_iff (S := fun _ : HeadFeature ↦ Srtᵒᵈ)).trans
    (forall_congr' fun f ↦ compat_toDual_iff (a := ℓ f) (b := r f))

instance (ℓ r : Specification) : Decidable (Compat (α := HeadFeature → Srtᵒᵈ) ℓ r) :=
  decidable_of_iff _ compat_iff.symm

end Specification

/-! ### Listemes -/

/-- (17b): a lexical verb is `[AUX −]` and `[INV −]`. -/
def lexicalVerb : Specification := .of .minus .minus

/-- (25): the modal *can* is finite, with `AUX` and `INV` open. -/
def modal : Specification := .of (vf := .fin)

/-- (35): auxiliary *do* is finite and `[AUX +]`. -/
def auxDo : Specification := .of (aux := .plus) (vf := .fin)

/-- The modal *better* is finite and `[INV −]`. -/
def better : Specification := .of (inv := .minus) (vf := .fin)

/-- (111): the word *aren't* with a first person singular subject, which a contraction
construction licenses, is finite and `[INV +]`. -/
def arentFirstSingular : Specification := .of (inv := .plus) (vf := .fin)

/-- (45): the listeme of *shall* in each of its senses. Deontic *shall* is `[INV +]`, and
futurate *shall* leaves `INV` open as other modals do. -/
def shall : Examples.Reading → Specification
  | .deontic => .of (inv := .plus) (vf := .fin)
  | .futurate => modal

/-- The specifications of the verb of an example: of each listeme of the verb, with *could* and
*will* modals as *can* is, or of the word itself for *aren't*. -/
def Examples.Verb.specifications : Examples.Verb → List Specification
  | .could | .will => [modal]
  | .shall => [SagEtAl2020.shall .deontic, SagEtAl2020.shall .futurate]
  | .better => [SagEtAl2020.better]
  | .doAux => [auxDo]
  | .arent => [arentFirstSingular]
  | .help | .seem => [lexicalVerb]

/-! ### Constructions -/

/-- The three headed constructions, each of which specifies the head features of its head
daughter. -/
inductive Headed where
  | subjHead
  | predHdComp
  | auxInitial
  deriving DecidableEq, Fintype, Repr

namespace Headed

/-- The construct sort that a construction constrains. -/
def sort : Headed → Srt
  | .subjHead => .subjHeadCxt
  | .predHdComp => .predHdCompCxt
  | .auxInitial => .auxInitialCxt

/-- The specification of the head daughter. The head of a subject-head construct and of a
predicational head-complement construct (24) is `[AUX −]` and `[INV −]`, and the head of an
aux-initial construct (39) is `[INV +]`. -/
def head : Headed → Specification
  | .subjHead | .predHdComp => .of .minus .minus
  | .auxInitial => .of (inv := .plus)

/-- The construction: the head daughter of a construct of its sort satisfies the
specification. -/
def principle (c : Headed) : Constraint sig where
  sort := c.sort
  atoms := c.head.atoms [.HDDTR]

end Headed

/-- (23): the head daughter of a subject-predicate clause is finite. -/
def subjPredPrinciple : Constraint sig where
  sort := .subjPredCl
  atoms := [.sort [.HDDTR, .CAT, .VFORM] .fin]

/-- (40): the mother of a polar interrogative is an independent clause. -/
def polarIntPrinciple : Constraint sig where
  sort := .polarIntCl
  atoms := [.sort [.MTR, .CAT, .IC] .plus]

/-- The inverted exclamative construction: the mother is an independent clause. -/
def auxInitialExclPrinciple : Constraint sig where
  sort := .auxInitialExclCl
  atoms := [.sort [.MTR, .CAT, .IC] .plus]

/-- The constructions of the paper. -/
def principles : List (Constraint sig) :=
  [Headed.subjHead.principle, Headed.predHdComp.principle, Headed.auxInitial.principle,
    subjPredPrinciple, polarIntPrinciple, auxInitialExclPrinciple]

/-- The filler-gap grammar with the constructions of the paper. -/
abbrev grammar : Grammar sig := .ofConstraints (constraints ++ principles)

namespace Examples.Clause

/-- The construct sort of a clause type. -/
def sort : Examples.Clause → Srt
  | .subjPred => .subjPredCl
  | .polarInt => .polarIntCl
  | .auxInitialExcl => .auxInitialExclCl

/-- The headed construction that a clause type instantiates. -/
def headed : Examples.Clause → Headed
  | .subjPred => .subjHead
  | .polarInt | .auxInitialExcl => .auxInitial

/-- The specification that the constructions of a clause type together require of its head
daughter: that of its headed construction, with a finite verb form in a subject-predicate clause
and a finite or infinitival one in the other two, which are core clauses. -/
def head : Examples.Clause → Specification
  | .subjPred => .of .minus .minus .fin
  | .polarInt | .auxInitialExcl => .of (inv := .plus) (vf := .core)

/-- The semantic type of the mother of a clause, that of the clause type of [sag-2010] it
belongs to: a declarative clause is austinean, an interrogative clause denotes a question and an
exclamative clause a fact. -/
def sem : Examples.Clause → Srt
  | .subjPred => .austinean
  | .polarInt => .question
  | .auxInitialExcl => .fact

end Examples.Clause

-- Figure 10 and the hierarchy of the appendix
theorem map_sort_inherited :
    (Constraint.inherited (constraints ++ principles) .polarIntCl).map (·.sort) =
        [.headedCxt, .coreCl, .interrogativeCl, .auxInitialCxt, .polarIntCl] ∧
      (Constraint.inherited (constraints ++ principles) .auxInitialExclCl).map (·.sort) =
        [.headedCxt, .coreCl, .exclamativeCl, .auxInitialCxt, .auxInitialExclCl] ∧
      (Constraint.inherited (constraints ++ principles) .subjPredCl).map (·.sort) =
        [.headedCxt, .coreCl, .declarativeCl, .subjHeadCxt, .subjPredCl] := by
  decide +kernel

variable {U : Type*} {I : Interpretation sig U} {u u' : U}

theorem sortAt_hdDtr (hI : I.Models grammar) (c : Headed) (hu : I.S u ≤ c.sort)
    (f : HeadFeature) : I.SortAt u [.HDDTR, .CAT, f.attr] (c.head f) :=
  Specification.forall_mem_atoms.1
    (fun _ ha ↦ hI.holds (c := c.principle) (by cases c <;> decide) hu ha) f

theorem sortAt_hdDtr_clause (hI : I.Models grammar) (k : Examples.Clause)
    (hu : I.S u ≤ k.sort) (f : HeadFeature) :
    I.SortAt u [.HDDTR, .CAT, f.attr] (k.head f) := by
  have hcore : I.S u ≤ .coreCl := hu.trans (by cases k <;> decide)
  have hheaded : I.S u ≤ k.headed.sort := hu.trans (by cases k <;> decide)
  have hvf := (sortAt_mtr_cat_iff hI.of_append_left
    (hu.trans (by cases k <;> decide : k.sort ≤ .headedCxt)) [.VFORM] .core).1
    (hI.sortAt corePrinciple hcore)
  cases k <;> cases f
  · exact sortAt_hdDtr hI .subjHead hheaded .aux
  · exact sortAt_hdDtr hI .subjHead hheaded .inv
  · exact hI.sortAt subjPredPrinciple hu
  · exact sortAt_hdDtr hI .auxInitial hheaded .aux
  · exact sortAt_hdDtr hI .auxInitial hheaded .inv
  · exact hvf
  · exact sortAt_hdDtr hI .auxInitial hheaded .aux
  · exact sortAt_hdDtr hI .auxInitial hheaded .inv
  · exact hvf

/-! ### Worked constructs -/

/-- The entities of a worked construct are the construct, its mother and head daughter, the
verbal category they share, the values of its three head features and of `IC`, and the mother's
semantic object. -/
inductive Ent where
  | cxt
  | mtr
  | hd
  | cat
  | aux
  | inv
  | vform
  | ic
  | sem
  deriving DecidableEq, Fintype, Repr

/-- The construct of sort `σ` whose mother and head daughter share a verbal category with head
features of the sorts `ℓ` and an `IC` value of sort `ic`, and whose mother has the semantic type
`semSort`. -/
@[reducible] def construct (σ : Srt) (ℓ : Specification) (ic semSort : Srt) :
    Interpretation sig Ent where
  S
    | .cxt => σ
    | .mtr | .hd => .overtExpr
    | .cat => .verb
    | .aux => ℓ .aux
    | .inv => ℓ .inv
    | .vform => ℓ .vform
    | .ic => ic
    | .sem => semSort
  A
    | .MTR, .cxt => some .mtr
    | .HDDTR, .cxt => some .hd
    | .CAT, .mtr | .CAT, .hd => some .cat
    | .AUX, .cat => some .aux
    | .INV, .cat => some .inv
    | .VFORM, .cat => some .vform
    | .IC, .cat => some .ic
    | .SEM, .mtr => some .sem
    | _, _ => none
  R := noRel

/-- The verb forms. -/
def vforms : List Srt := [.presentPart, .perfectPart, .passivePart, .fin, .inf, .base, .gerund]

theorem models_construct_iff (c : Headed) :
    ∀ a ∈ [Srt.plus, .minus], ∀ i ∈ [Srt.plus, .minus], ∀ v ∈ vforms,
      ((construct c.sort (.of a i v) .plus .austinean).Models grammar ↔
        a ≤ c.head .aux ∧ i ≤ c.head .inv ∧ v ≤ c.head .vform) := by
  cases c <;> decide +kernel

theorem isWellTyped_construct (c : Headed) :
    ∀ a ∈ [Srt.plus, .minus], ∀ i ∈ [Srt.plus, .minus], ∀ v ∈ vforms,
      (construct c.sort (.of a i v) .plus .austinean).IsWellTyped := by
  cases c <;> decide +kernel

theorem models_clause_construct_iff (k : Examples.Clause) :
    ∀ a ∈ [Srt.plus, .minus], ∀ i ∈ [Srt.plus, .minus], ∀ v ∈ vforms,
      ((construct k.sort (.of a i v) .plus k.sem).Models grammar ↔
        a ≤ k.head .aux ∧ i ≤ k.head .inv ∧ v ≤ k.head .vform) := by
  cases k <;> decide +kernel

theorem isWellTyped_clause_construct (k : Examples.Clause) :
    ∀ a ∈ [Srt.plus, .minus], ∀ i ∈ [Srt.plus, .minus], ∀ v ∈ vforms,
      (construct k.sort (.of a i v) .plus k.sem).IsWellTyped := by
  cases k <;> decide +kernel

-- (40), the inverted exclamative construction and Figure 11
theorem models_clause_iff (k : Examples.Clause) :
    ∀ ic ∈ [Srt.plus, .minus], ∀ s ∈ [Srt.austinean, .question, .fact, .modifier],
      ((construct k.sort (if k = .subjPred then .of .minus .minus .fin else .of .plus .plus .fin)
          ic s).Models grammar ↔ (k = .subjPred ∨ ic = .plus) ∧ s = k.sem) := by
  cases k <;> decide +kernel

/-! ### Heading a construction -/

/-- A category with the specification `ℓ` can head a construct of sort `σ` when it is
satisfiable over the grammar that an entity is of the sort `σ` and its head daughter satisfies
`ℓ`. -/
def CanHead (ℓ : Specification) (σ : Srt) : Prop :=
  grammar.IsSatisfiable (PathAtom.toDescription '' {a | a ∈ .sort [] σ :: ℓ.atoms [.HDDTR]})

theorem canHead_iff_exists {ℓ : Specification} {σ : Srt} :
    CanHead ℓ σ ↔ ∃ (U : Type) (I : Interpretation sig U), I.IsWellTyped ∧ I.Models grammar ∧
      ∃ u, I.S u ≤ σ ∧ ∀ f : HeadFeature, I.SortAt u [.HDDTR, .CAT, f.attr] (ℓ f) := by
  simp only [CanHead, Grammar.isSatisfiable_image_toDescription_iff, List.forall_mem_cons,
    PathAtom.holds_sort, Specification.forall_mem_atoms, List.cons_append, List.nil_append]
  exact exists_congr fun _ ↦ exists_congr fun _ ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
    exists_congr fun _ ↦ and_congr_left fun _ ↦ Interpretation.sortAt_nil

private theorem exists_species_le :
    (∀ τ : Srt, τ ≤ .boolean → ∃ a ∈ [Srt.plus, .minus], a ≤ τ) ∧
      ∀ τ : Srt, τ ≤ .vform → ∃ v ∈ vforms, v ≤ τ := by
  decide +kernel

-- if the grammar requires `r` of the head of a construct of sort `σ` and the worked constructs
-- with head features below `r` are models, heading `σ` is compatibility with `r`
private theorem canHead_iff_of {ℓ r : Specification} {σ ic sem : Srt}
    (hr : r .aux ≤ .boolean ∧ r .inv ≤ .boolean ∧ r .vform ≤ .vform)
    (hsat : ∀ {U : Type} {I : Interpretation sig U} {u : U}, I.Models grammar → I.S u ≤ σ →
      ∀ f : HeadFeature, I.SortAt u [.HDDTR, .CAT, f.attr] (r f))
    (hmod : ∀ a ∈ [Srt.plus, .minus], ∀ i ∈ [Srt.plus, .minus], ∀ v ∈ vforms,
      a ≤ r .aux → i ≤ r .inv → v ≤ r .vform →
        (construct σ (.of a i v) ic sem).Models grammar ∧
          (construct σ (.of a i v) ic sem).IsWellTyped) :
    CanHead ℓ σ ↔ ∀ f, ∃ τ, τ ≤ ℓ f ∧ τ ≤ r f := by
  rw [canHead_iff_exists]
  constructor
  · rintro ⟨U, I, -, hI, u, hu, hℓ⟩ f
    exact (hℓ f).exists_le (hsat hI hu f)
  · intro h
    obtain ⟨τa, haℓ, har⟩ := h .aux
    obtain ⟨τi, hiℓ, hir⟩ := h .inv
    obtain ⟨τv, hvℓ, hvr⟩ := h .vform
    obtain ⟨a, ha, haτ⟩ := exists_species_le.1 τa (har.trans hr.1)
    obtain ⟨i, hi, hiτ⟩ := exists_species_le.1 τi (hir.trans hr.2.1)
    obtain ⟨v, hv, hvτ⟩ := exists_species_le.2 τv (hvr.trans hr.2.2)
    obtain ⟨hM, hW⟩ := hmod a ha i hi v hv (haτ.trans har) (hiτ.trans hir) (hvτ.trans hvr)
    refine ⟨Ent, _, hW, hM, .cxt, le_rfl, fun f ↦ ?_⟩
    cases f
    exacts [⟨.aux, rfl, haτ.trans haℓ⟩, ⟨.inv, rfl, hiτ.trans hiℓ⟩, ⟨.vform, rfl, hvτ.trans hvℓ⟩]

/-- A specification can head a headed construction exactly when it is compatible with the
specification that the construction requires of its head daughter. -/
theorem canHead_iff (ℓ : Specification) (c : Headed) :
    CanHead ℓ c.sort ↔ Compat (α := HeadFeature → Srtᵒᵈ) ℓ c.head :=
  (canHead_iff_of (by cases c <;> decide) (fun hI hu ↦ sortAt_hdDtr hI c hu)
    fun a ha i hi v hv h₁ h₂ h₃ ↦ ⟨(models_construct_iff c a ha i hi v hv).2 ⟨h₁, h₂, h₃⟩,
      isWellTyped_construct c a ha i hi v hv⟩).trans Specification.compat_iff.symm

-- the head of a clause is also finite, or finite or infinitival
theorem canHead_clause_iff (ℓ : Specification) (k : Examples.Clause) :
    CanHead ℓ k.sort ↔ Compat (α := HeadFeature → Srtᵒᵈ) ℓ k.head :=
  (canHead_iff_of (by cases k <;> decide) (fun hI hu ↦ sortAt_hdDtr_clause hI k hu)
    fun a ha i hi v hv h₁ h₂ h₃ ↦ ⟨(models_clause_construct_iff k a ha i hi v hv).2 ⟨h₁, h₂, h₃⟩,
      isWellTyped_clause_construct k a ha i hi v hv⟩).trans Specification.compat_iff.symm

/-- The examples that the constructions here do not account for. Stressed *do* heads a
subject-predicate clause (36b), which the rebuttal construction licenses, and *do* does not
precede a grammatical verb (12a), which `GRAM` excludes. -/
def unaccounted : List Examples.Example := [.ex_12a_did, .ex_36b]

/-- Each example other than the two unaccounted for is acceptable exactly when some
specification of its verb can head a clause of its type. -/
theorem judgments (x : Examples.Example) (hx : x ∉ unaccounted) :
    ∃ v k, x.verb = some v ∧ x.clause = some k ∧
      (x.datum.judgment = .acceptable ↔ ∃ ℓ ∈ v.specifications, CanHead ℓ k.sort) := by
  simp only [canHead_clause_iff]
  revert x
  decide +kernel

theorem judgments_unaccounted :
    ∀ x ∈ unaccounted, ∃ v k, x.verb = some v ∧ x.clause = some k ∧
      ¬ (x.datum.judgment = .acceptable ↔ ∃ ℓ ∈ v.specifications, CanHead ℓ k.sort) := by
  simp only [canHead_clause_iff]
  decide +kernel

/-- A sense of *shall* is available in an example exactly when the listeme with that sense can
head a clause of the example's type. -/
theorem shall_readings (x : Examples.Example) (r : Examples.Reading) :
    ∀ j ∈ x.reading r, ∃ k, x.clause = some k ∧
      (j = .acceptable ↔ CanHead (shall r) k.sort) := by
  simp only [canHead_clause_iff]
  revert x r
  decide +kernel

/-! ### Aux-initial clauses as head daughters -/

theorem sortAt_mtr_inv (hI : I.Models grammar) (hu : I.S u ≤ .auxInitialCxt) :
    I.SortAt u [.MTR, .CAT, .INV] .plus :=
  (sortAt_mtr_cat_iff hI.of_append_left (hu.trans (by decide)) [.INV] .plus).2
    (sortAt_hdDtr hI .auxInitial hu .inv)

/-- The mother of an aux-initial construct is inverted, so it is not the head daughter of a
construct whose head is uninverted: a subject-head construct, a predicational head-complement
construct, a topicalized clause, a wh-exclamative or a wh-relative. -/
theorem mtr_ne_hdDtr (hI : I.Models grammar) (hu : I.S u ≤ .auxInitialCxt)
    (hu' : I.S u' ≤ .subjHeadCxt ∨ I.S u' ≤ .predHdCompCxt ∨ I.S u' ≤ .topCl ∨
      I.S u' ≤ .whExclCl ∨ I.S u' ≤ .whRelCl) {s : U} (hs : I.A .MTR u = some s) :
    I.A .HDDTR u' ≠ some s := by
  intro hs'
  have hminus : I.SortAt u' [.HDDTR, .CAT, .INV] .minus := by
    rcases hu' with h | h | h | h | h
    · exact sortAt_hdDtr hI .subjHead h .inv
    · exact sortAt_hdDtr hI .predHdComp h .inv
    · exact Sag2010.sortAt_hdDtr_inv hI.of_append_left (c := .topicalized) (.inl rfl) h
    · exact Sag2010.sortAt_hdDtr_inv hI.of_append_left (c := .whExclamative) (.inr (.inl rfl)) h
    · exact Sag2010.sortAt_hdDtr_inv hI.of_append_left (c := .whRelative) (.inr (.inr rfl)) h
  obtain ⟨ρ, hplus, hminus⟩ := ((Interpretation.sortAt_cons hs).1
    (sortAt_mtr_inv hI hu)).exists_le ((Interpretation.sortAt_cons hs').1 hminus)
  exact (by decide +kernel : ∀ ρ : Srt, ρ ≤ .plus → ¬ ρ ≤ .minus) ρ hplus hminus

/-- A nonsubject wh-interrogative whose head daughter is the mother of an aux-initial construct
is an independent clause, since its head is inverted exactly when it is independent. -/
theorem sortAt_hdDtr_ic (hI : I.Models grammar) (hu : I.S u ≤ .auxInitialCxt)
    (hu' : I.S u' ≤ .nsWhIntCl) {s : U} (hs : I.A .MTR u = some s)
    (hs' : I.A .HDDTR u' = some s) : I.SortAt u' [.HDDTR, .CAT, .IC] .plus :=
  (hI.pathEq nsWhIntPrinciple hu' (p := [.HDDTR, .CAT, .INV])
    (q := [.HDDTR, .CAT, .IC])).sortAt_iff.1
    ((Interpretation.sortAt_cons hs').2 ((Interpretation.sortAt_cons hs).1
      (sortAt_mtr_inv hI hu)))

/-- The entities of a worked wh-interrogative with an aux-initial head: the two constructs, the
mother, filler daughter and semantic object of the interrogative, the filler's category and
index, the mother and head daughter of the aux-initial construct with the verbal category that
they share with the interrogative's mother, the one-gap list, its gap and the empty list, and
the values of the head features. -/
inductive WhEnt where
  | wh | whMtr | fl | flCat | ix | whSem | cxt | mtr | hd | cat | gaps | gp | nil | plus | minus
  | fin
  deriving DecidableEq, Fintype, Repr

/-- A nonsubject wh-interrogative such as *Who did Kim see?*, whose head daughter is the mother
of an aux-initial construct with a finite, inverted `[AUX +]` head and one gap, which the filler
fills. The shared category has the `IC` value `ic`. -/
@[reducible] def whConstruct (ic : WhEnt) : Interpretation sig WhEnt where
  S
    | .wh => .nsWhIntCl
    | .cxt => .auxInitialCxt
    | .whMtr | .fl | .mtr | .hd => .overtExpr
    | .flCat => .noun
    | .cat => .verb
    | .ix => .idx
    | .whSem => .question
    | .gaps => .nelist
    | .gp => .gap
    | .nil => .elist
    | .plus => .plus
    | .minus => .minus
    | .fin => .fin
  A
    | .MTR, .wh => some .whMtr
    | .HDDTR, .wh | .MTR, .cxt => some .mtr
    | .FILLERDTR, .wh => some .fl
    | .HDDTR, .cxt => some .hd
    | .CAT, .whMtr | .CAT, .mtr | .CAT, .hd => some .cat
    | .CAT, .fl | .CAT, .gp => some .flCat
    | .INDEX, .fl | .INDEX, .gp => some .ix
    | .AUX, .cat | .INV, .cat => some .plus
    | .IC, .cat => some ic
    | .VFORM, .cat => some .fin
    | .GAP, .mtr => some .gaps
    | .FIRST, .gaps => some .gp
    | .REST, .gaps | .GAP, .whMtr | .GAP, .fl | .GAP, .gp => some .nil
    | .SEM, .whMtr => some .whSem
    | _, _ => none
  R := noRel

theorem models_whConstruct_iff :
    ∀ ic ∈ [WhEnt.plus, .minus], ((whConstruct ic).Models grammar ↔ ic = .plus) := by
  decide +kernel

theorem isWellTyped_whConstruct : ∀ ic ∈ [WhEnt.plus, .minus], (whConstruct ic).IsWellTyped := by
  decide +kernel

end SagEtAl2020
