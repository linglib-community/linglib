module

public import Linglib.Syntax.HPSG.Construction
public import Linglib.Data.Examples.SagEtAl2020
public import Studies.Sag2010

/-!
# Sag et al. (2020): Lessons from the English Auxiliary System

A verbal category has the features `AUX` and `INV`, each with a positive or a negative value, and
a verb form. The listeme of a verb specifies some of these features and leaves the others open:
a lexical verb is `[AUX −]` and `[INV −]`, auxiliary *do* is `[AUX +]`, *better* is `[INV −]`,
deontic *shall* and first-person *aren't* are `[INV +]`, and a modal such as *can* specifies
neither. A construction specifies the features of its head daughter in the same way. The head of
a subject-predicate clause is finite, `[AUX −]` and `[INV −]`, the head of a predicational
head-complement construct is `[AUX −]` and `[INV −]`, and the head of an aux-initial construct is
`[INV +]`.

We define a *specification* as a sort for each of the three features, an open feature having the
sort of all its values, and state the three constructions on the construct hierarchy of
`Linglib/Syntax/HPSG/Construction.lean`. A specified category *can head* a construct sort when
some well-typed model of the grammar has a construct of that sort whose head daughter satisfies
the specification. The main result, `SagEtAl2020.canHead_iff`, says that it can exactly when, for
each feature, the sort of the listeme and the sort of the construction have a common subsort. An
example is acceptable exactly when a listeme of its verb can head its clause
(`SagEtAl2020.judgments`), and a sense of *shall* is available exactly where the listeme with
that sense can (`SagEtAl2020.shall_readings`).

The mother of an aux-initial construct has the category of its head daughter and so is inverted.
It is therefore not the head daughter of a construct whose head is uninverted, among them the
topicalized clauses, wh-exclamatives and wh-relatives of [sag-2010]
(`SagEtAl2020.mtr_ne_hdDtr`). A polar interrogative and an inverted exclamative are aux-initial
constructs and clauses of their type, and inherit the constraints on both: the mother is an
independent clause that denotes a question or a fact (`SagEtAl2020.models_clause_iff`).

## Implementation notes

The valence conditions of the constructions are not stated: that the head daughter of an
aux-initial or a head-complement construct is a word whose valents are its sisters, and that the
mother of an aux-initial construct is saturated. The signature has no `VAL`, no `GRAM` and no
distinction of words from phrases, so the verb form that an auxiliary selects and the complement
of *do* are not constrained, and a listeme is its specification of the head features.

As in the paper the hierarchy of constructs is partial, so a construct may bear the sort of the
aux-initial construction itself, and the models that `SagEtAl2020.CanHead` ranges over are
well-typed and not sort-resolved.

The predicational head-complement construction has the `[AUX −]` head of its display, so
auxiliary *do* heads no head-complement construct here.

## TODO

* An aux-initial clause as the head daughter of the nonsubject wh-interrogative of [sag-2010],
  whose head is inverted exactly when it is independent. A worked model needs both constructs.
* The lexical constructions of the paper: negation, contraction, ellipsis and rebuttal.

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
def of (aux inv : Srt := .boolean) (vform : Srt := .vform) : Specification
  | .aux => aux
  | .inv => inv
  | .vform => vform

/-- The formula that says of the sign at the end of the path `p` that each head feature of its
category has a value of the specified sort. -/
def toFormula (ℓ : Specification) (p : Path sig := []) : Formula sig :=
  .conj ([HeadFeature.aux, .inv, .vform].map fun f ↦
    .sortAssign (.path (p ++ [.CAT, f.attr])) (ℓ f))

@[simp] theorem freeVars_toFormula (ℓ : Specification) (p : Path sig) :
    (ℓ.toFormula p).freeVars = ∅ := by
  simp [toFormula, Formula.conj, Formula.top, Formula.freeVars, Term.freeVars]

variable {U : Type*} {I : Interpretation sig U} {g : ℕ → U} {u : U}

theorem satisfies_toFormula {ℓ : Specification} {p : Path sig} :
    I.Satisfies g u (ℓ.toFormula p) ↔
      ∀ f : HeadFeature, I.Satisfies g u (.sortAssign (.path (p ++ [.CAT, f.attr])) (ℓ f)) := by
  rw [toFormula, Interpretation.satisfies_conj, List.forall_mem_map]
  exact ⟨fun h f ↦ h f (by cases f <;> simp), fun h f _ ↦ h f⟩

end Specification

/-! ### Listemes -/

/-- (17b): a lexical verb is `[AUX −]` and `[INV −]`. -/
def lexicalVerb : Specification := .of .minus .minus

/-- (25): the modal *can* is finite, with `AUX` and `INV` open. -/
def modal : Specification := .of (vform := .fin)

/-- (35): auxiliary *do* is finite and `[AUX +]`. -/
def auxDo : Specification := .of (aux := .plus) (vform := .fin)

/-- The modal *better* is finite and `[INV −]`. -/
def better : Specification := .of (inv := .minus) (vform := .fin)

/-- (111): *aren't* with a first person singular subject is finite and `[INV +]`. -/
def arentFirstSingular : Specification := .of (inv := .plus) (vform := .fin)

/-- (45): the listeme of *shall* in each of its senses. Deontic *shall* is `[INV +]`, and
futurate *shall* leaves `INV` open as other modals do. -/
def shall : Examples.Reading → Specification
  | .deontic => .of (inv := .plus) (vform := .fin)
  | .futurate => modal

/-- The listemes of the verb of an example. -/
def Examples.Verb.listemes : Examples.Verb → List Specification
  | .can | .will => [modal]
  | .shall => [shall .deontic, shall .futurate]
  | .better => [better]
  | .doAux => [auxDo]
  | .arent => [arentFirstSingular]
  | .help | .seem => [lexicalVerb]

/-! ### Constructions -/

/-- The headed constructions that specify the head features of their head daughter. -/
inductive Headed where
  | subjPred
  | predHdComp
  | auxInitial
  deriving DecidableEq, Fintype, Repr

namespace Headed

/-- The construct sort that a construction constrains. -/
def sort : Headed → Srt
  | .subjPred => .subjPredCl
  | .predHdComp => .predHdCompCxt
  | .auxInitial => .auxInitialCxt

/-- The specification of the head daughter. The head of a subject-predicate clause (23) is
finite, `[AUX −]` and `[INV −]`, the head of a predicational head-complement construct (24) is
`[AUX −]` and `[INV −]`, and the head of an aux-initial construct (39) is `[INV +]`. -/
def head : Headed → Specification
  | .subjPred => .of .minus .minus .fin
  | .predHdComp => .of .minus .minus
  | .auxInitial => .of (inv := .plus)

/-- The construction: the head daughter of a construct of its sort satisfies the
specification. -/
def principle (c : Headed) : Constraint sig where
  sort := c.sort
  body := c.head.toFormula [.HDDTR]
  freeVars_body := c.head.freeVars_toFormula _

end Headed

/-- (40): the mother of a polar interrogative is an independent clause. -/
def polarIntPrinciple : Constraint sig where
  sort := .polarIntCl
  body := .sortAssign (.path [.MTR, .CAT, .IC]) .plus

/-- The inverted exclamative construction: the mother is an independent clause. -/
def auxInitialExclPrinciple : Constraint sig where
  sort := .auxInitialExclCl
  body := .sortAssign (.path [.MTR, .CAT, .IC]) .plus

/-- The constructions of the paper. -/
def principles : List (Constraint sig) :=
  [Headed.subjPred.principle, Headed.predHdComp.principle, Headed.auxInitial.principle,
    polarIntPrinciple, auxInitialExclPrinciple]

/-- The filler-gap grammar with the constructions of the paper. -/
abbrev grammar : Grammar sig :=
  .ofList ((constraints ++ principles).map Constraint.toDescription)

/-- The construct sort of a clause type. -/
def Examples.Clause.sort : Examples.Clause → Srt
  | .subjPred => .subjPredCl
  | .polarInt => .polarIntCl
  | .auxInitialExcl => .auxInitialExclCl

/-- The headed construction that a clause type instantiates. -/
def Examples.Clause.headed : Examples.Clause → Headed
  | .subjPred => .subjPred
  | .polarInt | .auxInitialExcl => .auxInitial

/-- The semantic type of the mother of a clause: a subject-predicate clause is austinean, a
polar interrogative denotes a question and an inverted exclamative a fact. -/
def Examples.Clause.sem : Examples.Clause → Srt
  | .subjPred => .austinean
  | .polarInt => .question
  | .auxInitialExcl => .fact

-- Figure 10
theorem map_sort_inherited :
    (Constraint.inherited (constraints ++ principles) .polarIntCl).map (·.sort) =
        [.headedCxt, .coreCl, .interrogativeCl, .auxInitialCxt, .polarIntCl] ∧
      (Constraint.inherited (constraints ++ principles) .auxInitialExclCl).map (·.sort) =
        [.headedCxt, .coreCl, .exclamativeCl, .auxInitialCxt, .auxInitialExclCl] ∧
      (Constraint.inherited (constraints ++ principles) .subjPredCl).map (·.sort) =
        [.headedCxt, .coreCl, .declarativeCl, .subjPredCl] := by
  decide +kernel

variable {U : Type*} {I : Interpretation sig U} {u u' : U}

theorem models_fillerGap (hI : I.Models grammar) : I.Models HPSG.Construction.grammar :=
  hI.mono fun _ hd ↦
    let ⟨c, hc, e⟩ := List.mem_map.1 hd
    List.mem_map.2 ⟨c, List.mem_append_left _ hc, e⟩

theorem satisfies_body (hI : I.Models grammar) {c : Constraint sig}
    (hc : c ∈ constraints ++ principles) (hu : I.S u ≤ c.sort) :
    I.Satisfies (fun _ ↦ u) u c.body :=
  hI.satisfies_body (List.mem_map_of_mem hc) hu

theorem satisfies_hdDtr (hI : I.Models grammar) (c : Headed) (hu : I.S u ≤ c.sort)
    (f : HeadFeature) :
    I.Satisfies (fun _ ↦ u) u (.sortAssign (.path [.HDDTR, .CAT, f.attr]) (c.head f)) :=
  Specification.satisfies_toFormula.1
    (satisfies_body hI (c := c.principle) (by cases c <;> simp [principles]) hu) f

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

/-- A worked subject-predicate clause, polar interrogative or inverted exclamative with a finite
head, uninverted in the first and inverted in the others as in Figure 11, is a model of the
grammar exactly when its mother has the semantic type of its clause type and, if it is
aux-initial, is independent. -/
theorem models_clause_iff (k : Examples.Clause) :
    ∀ ic ∈ [Srt.plus, .minus], ∀ s ∈ [Srt.austinean, .question, .fact, .modifier],
      ((construct k.sort (if k = .subjPred then .of .minus .minus .fin else .of .plus .plus .fin)
          ic s).Models grammar ↔ (k = .subjPred ∨ ic = .plus) ∧ s = k.sem) := by
  cases k <;> decide +kernel

/-! ### Heading a construction -/

/-- A category with the specification `ℓ` can head a construct of sort `σ` when, in some
well-typed model of the grammar, the head daughter of a construct of that sort satisfies `ℓ`. -/
def CanHead (ℓ : Specification) (σ : Srt) : Prop :=
  ∃ (U : Type) (I : Interpretation sig U), I.Models grammar ∧ I.IsWellTyped ∧
    ∃ u h, I.S u ≤ σ ∧ I.A .HDDTR u = some h ∧ I.Satisfies (fun _ ↦ h) h ℓ.toFormula

private theorem exists_species_le (c : Headed) :
    (∀ τ, τ ≤ c.head .aux → ∃ a ∈ [Srt.plus, .minus], a ≤ τ) ∧
      (∀ τ, τ ≤ c.head .inv → ∃ i ∈ [Srt.plus, .minus], i ≤ τ) ∧
        ∀ τ, τ ≤ c.head .vform → ∃ v ∈ vforms, v ≤ τ := by
  cases c <;> decide +kernel

/-- A listeme can head a construction exactly when, for each head feature, the sort that the
listeme gives it and the sort that the construction requires of its head daughter have a common
subsort. -/
theorem canHead_iff (ℓ : Specification) (c : Headed) :
    CanHead ℓ c.sort ↔ ∀ f, ∃ τ, τ ≤ ℓ f ∧ τ ≤ c.head f := by
  constructor
  · rintro ⟨U, I, hI, -, u, h, hu, hh, hℓ⟩ f
    exact (Specification.satisfies_toFormula.1 hℓ f).exists_le_of_sortAssign
      ((Interpretation.satisfies_sortAssign_path_cons hh).1 (satisfies_hdDtr hI c hu f))
  · intro h
    obtain ⟨τa, haℓ, hac⟩ := h .aux
    obtain ⟨τi, hiℓ, hic⟩ := h .inv
    obtain ⟨τv, hvℓ, hvc⟩ := h .vform
    obtain ⟨a, ha, haτ⟩ := (exists_species_le c).1 τa hac
    obtain ⟨i, hi, hiτ⟩ := (exists_species_le c).2.1 τi hic
    obtain ⟨v, hv, hvτ⟩ := (exists_species_le c).2.2 τv hvc
    refine ⟨Ent, construct c.sort (.of a i v) .plus .austinean,
      (models_construct_iff c a ha i hi v hv).2 ⟨haτ.trans hac, hiτ.trans hic, hvτ.trans hvc⟩,
      isWellTyped_construct c a ha i hi v hv, .cxt, .hd, le_rfl, rfl,
      Specification.satisfies_toFormula.2 fun f ↦ ?_⟩
    cases f
    exacts [⟨.aux, rfl, haτ.trans haℓ⟩, ⟨.inv, rfl, hiτ.trans hiℓ⟩, ⟨.vform, rfl, hvτ.trans hvℓ⟩]

/-- Each example is acceptable exactly when some listeme of its verb can head the construction
that its clause type instantiates. -/
theorem judgments (x : Examples.Example) :
    ∃ v k, x.verb = some v ∧ x.clause = some k ∧
      (x.datum.judgment = .acceptable ↔ ∃ ℓ ∈ v.listemes, CanHead ℓ k.headed.sort) := by
  simp only [canHead_iff]
  revert x
  decide +kernel

/-- A sense of *shall* is available in an example exactly when the listeme with that sense can
head the construction that the clause type of the example instantiates. -/
theorem shall_readings (x : Examples.Example) (r : Examples.Reading) :
    ∀ j ∈ x.reading r, ∃ k, x.clause = some k ∧
      (j = .acceptable ↔ CanHead (shall r) k.headed.sort) := by
  simp only [canHead_iff]
  revert x r
  decide +kernel

/-! ### Aux-initial clauses as head daughters -/

theorem satisfies_mtr_inv (hI : I.Models grammar) (hu : I.S u ≤ .auxInitialCxt) :
    I.Satisfies (fun _ ↦ u) u (.sortAssign (.path [.MTR, .CAT, .INV]) .plus) :=
  (satisfies_hdCat_iff (models_fillerGap hI) (hu.trans (by decide)) [.INV] .plus).2
    (satisfies_hdDtr hI .auxInitial hu .inv)

/-- The mother of an aux-initial construct is inverted, so it is not the head daughter of a
construct whose head is uninverted: a subject-predicate clause, a predicational head-complement
construct, a topicalized clause, a wh-exclamative or a wh-relative. -/
theorem mtr_ne_hdDtr (hI : I.Models grammar) (hu : I.S u ≤ .auxInitialCxt)
    (hu' : I.S u' ≤ .subjPredCl ∨ I.S u' ≤ .predHdCompCxt ∨ I.S u' ≤ .topCl ∨
      I.S u' ≤ .whExclCl ∨ I.S u' ≤ .whRelCl) {s : U} (hs : I.A .MTR u = some s) :
    I.A .HDDTR u' ≠ some s := by
  intro hs'
  have hminus : I.Satisfies (fun _ ↦ u') u' (.sortAssign (.path [.HDDTR, .CAT, .INV]) .minus) := by
    rcases hu' with h | h | h | h | h
    · exact satisfies_hdDtr hI .subjPred h .inv
    · exact satisfies_hdDtr hI .predHdComp h .inv
    · exact Sag2010.satisfies_head_uninverted (models_fillerGap hI) (c := .topicalized)
        (.inl rfl) h
    · exact Sag2010.satisfies_head_uninverted (models_fillerGap hI) (c := .whExclamative)
        (.inr (.inl rfl)) h
    · exact Sag2010.satisfies_head_uninverted (models_fillerGap hI) (c := .whRelative)
        (.inr (.inr rfl)) h
  obtain ⟨ρ, hplus, hminus⟩ :=
    ((Interpretation.satisfies_sortAssign_path_cons (g' := fun _ ↦ s) hs).1
      (satisfies_mtr_inv hI hu)).exists_le_of_sortAssign
      ((Interpretation.satisfies_sortAssign_path_cons hs').1 hminus)
  exact (by decide +kernel : ∀ ρ : Srt, ρ ≤ .plus → ¬ ρ ≤ .minus) ρ hplus hminus

end SagEtAl2020
