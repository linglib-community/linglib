module

public import Linglib.Fragments.Ga.Pronouns
public import Linglib.Fragments.Ga.Verbs
public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Data.WALS.Features.F101A
public import Linglib.Syntax.Binding.MinimalPronoun
public import Linglib.Syntax.Control.Head
public import Studies.Landau2013
public import Linglib.Data.Examples.Allotey2021
public import Linglib.Data.Examples.Readers

/-!
# Allotey (2021): overt pronouns of infinitival predicates of Gã

Allotey studies obligatory control into Gã irrealis
`ni`-clauses requires an overt subject proclitic: null PRO is ungrammatical, a
lexical subject is ungrammatical, and the proclitic shows the whole OC signature
(Table 2). The controlled clause is non-finite and irrealis rather than
subjunctive — it bars tense and aspect, focus fronting and free reference,
licenses NPIs across its boundary, negates preverbally, and carries the irrealis
marker only as a high tone on its subject (Table 4). The pronoun is overt
because that tone needs a segmental host. The subject markers are pronouns,
not agreement: the verb is invariant across subjects (§4.4) and a marker
cannot double a lexical subject (§6.1), against Campbell's affixal analysis;
Gã is therefore a non-pro-drop language (§2.1). The WALS 101A coding of Gã,
made from Ablorh-Odjidja's grammar, is affixal too.

Everything is read off the paper's example rows and the Fragment. The control
profile of a clause type is Landau's signature as the rows attest it
(`Control.ofAttested`): no row attests a criterial configuration of the
`ni`-clause, so it is obligatory control, while the finite `akɛ`-clause attests
free reference. Complementizer selection is `Verb.Takes` over the Fragment's
frames; every finiteness diagnostic is a row theorem conditioned on the
complementizer's finiteness alone, the paper's convergence argument; Table 4 is
the exponents the rows show in each irrealis context, and the tone-hosting
requirement then derives the overt pronoun from the minimal-pronoun inventory.

## Implementation notes

The paper's pro-drop status is its own reading of its 101A cell, obligatory
subject pronouns (§4.2), and is stated here rather than in the Fragment because
WALS codes the same markers as affixes; `wals_codes_affixes` records
the discrepancy and `no_agreement_rows` the paper's evidence against it. The
bound-variable row of Table 2 rests on the *de se* example (53); the paper
has no *only* test, so `Control.Diagnostic.strictUnderOnly` is never attested
and the bound-variable clause of the signature holds unrefuted rather than
tested. The paper tests reference only in the `ni`- and `akɛ`-clauses, so the
comparison with Landau's scale of finiteness is stated for those two.

## References

* [allotey-2021]
* [ablorh-odjidja-1968]
* [campbell-2017]
* [landau-2013]
* [landau-2004]
* [szabolcsi-2009]
* [hornstein-1999]
* [satik-2019]
* [karttunen-1971]
* [noonan-2007]
* [rizzi-1997]
* [wals-2013]
* [wurmbrand-lohninger-2023]
* [wurmbrand-2024]
-/

@[expose] public section

namespace Allotey2021

open Binding.MinimalPronoun Control Ga Ga.Pronouns Morphology

/-! ### Pronouns (Table 3) -/

-- p. 25
theorem exists_syncretic_form_iff (r : Row) :
    (∃ f ∈ table (r, .subjective), ∀ k, f ∈ table (r, k)) ↔ r ≠ .sg2 ∧ r ≠ .sg3 ∧ r ≠ .imp := by
  cases r <;> decide

theorem objective_form_iff (r : Row) :
    (∃ f ∈ table (r, .objective), formCellsOf table f = {(r, .objective)}) ↔
      r = .sg2 ∨ r = .sg3 := by
  cases r <;> decide

-- p. 25
theorem possessive_subset_subjective (r : Row) :
    table (r, .possessive) ⊆ table (r, .subjective) := by
  cases r <;> decide

theorem paradigm_nonempty (c : Person.Category) : (paradigm c).Nonempty := by
  cases c <;> decide +kernel

theorem subjective_nonempty (r : Row) : (table (r, .subjective)).Nonempty := by
  cases r <;> decide

/-! ### Subject pronouns are not agreement (§4.4, §6.1) -/

theorem no_agreement_rows :
    (∀ row ∈ Examples.all, row.feature? "diagnostic" = some "agreement" →
      (row.feature? "person").isSome → ("tee", "went") ∈ row.glossedTokens) ∧
      ∃ r₁ ∈ Examples.all, ∃ r₂ ∈ Examples.all,
        r₁.feature? "diagnostic" = some "agreement" ∧
        r₂.feature? "diagnostic" = some "agreement" ∧
        r₁.feature? "person" ≠ r₂.feature? "person" := by
  decide +kernel

/-- In the paper's cell of [wals-2013]'s 101A, subject pronouns are obligatory and object
    pronouns omissible (§4.2). -/
def pronominalSubjects : Data.WALS.F101A.ExpressionOfPronominalSubjects :=
  .obligatoryPronounsInSubjectPosition

/-- [wals-2013] codes Gã `ga` as having subject affixes on the verb, the analysis of [campbell-2017]
that ex 123 and ex 125 argue against. -/
theorem wals_codes_affixes :
    Data.WALS.F101A.allData.lookup "ga" = some .subjectAffixesOnVerb := by
  decide +kernel

/-- The coding rests on [ablorh-odjidja-1968]; the affixal analysis of
    [campbell-2017] came later. -/
example : Data.WALS.F101A.sources.lookup "ga" = some ["Ablorh-Odjidja-1968[passim]"] := by
  decide +kernel

/-! ### Complementizer selection (§5.5.1) -/

theorem frame_takes_iff (c d : EmbeddedClauseType) :
    c.frame.Takes d.complementizer ↔ c = d := by
  cases c <;> cases d <;> decide

theorem takes_ni_iff_control :
    ∀ v ∈ verbs, v.Takes ni ↔ v.HasController := by
  decide

theorem proposition_iff_finite :
    ∀ v ∈ verbs, ∀ r ∈ v.readings, ∀ s ∈ r.size,
      (s = .proposition ↔ ∃ z ∈ complementizers, r.frame.Takes z ∧ z.IsFinite) := by
  decide

-- Table 2
theorem control_rows :
    (∃ v ∈ verbs, ∃ d ∈ v.valency.diatheses, d.controllerRole = some .S) ∧
      ∃ v ∈ verbs, ∃ d ∈ v.valency.diatheses, d.controllerRole = some .P := by
  decide

/-! ### Rows -/

/-- Gã has no context-specific vocabulary item for minimal pronouns, so the elsewhere pronoun
    realizes every context. -/
def gaInventory : Vocabulary Form where
  items := []
  elsewhere := .pronoun

/-- The Fragment entry for a row's matrix verb. -/
def verbOf (row : Datum) : Option Verb :=
  (row.feature? "verb").bind (Verb.find? verbs ·)

/-- The clause type a complementizer feature names. -/
def clauseOf : String → Option EmbeddedClauseType
  | "ni" => some .ni
  | "ake" => some .ake
  | "keji" => some .keji
  | _ => none

/-- A row's clause type is its complement's, or the finite type for a matrix clause the paper
    labels finite. -/
def clauseTypeOf (row : Datum) : Option EmbeddedClauseType :=
  match row.feature? "complementizer", row.feature? "clauseType" with
  | some c, _ => clauseOf c
  | none, some "finite" => some .ake
  | _, _ => none


/-- The realized form of a row's embedded subject. -/
def formOf (row : Datum) : Option Form :=
  match row.feature? "embeddedSubject" with
  | some "pronoun" => some .pronoun
  | some "null" => some .null
  | _ => none

theorem controlled_subject_rows :
    ∀ row ∈ Examples.all, row.feature? "diagnostic" ∈ [none, some "nullSubject"] →
      ∀ f ∈ formOf row, (row.judgment = .acceptable ↔ f = gaInventory.controlForm) := by
  decide +kernel

theorem lexical_subject_rows :
    ∀ row ∈ Examples.all, row.feature? "embeddedSubject" = some "lexical" →
      row.feature? "clauseContext" = none → row.judgment = .ungrammatical := by
  decide +kernel

theorem c_selection_rows :
    ∀ row ∈ Examples.all, row.feature? "diagnostic" = some "cSelection" →
      ∀ v ∈ verbOf row, ∀ c ∈ clauseTypeOf row,
        (row.judgment = .acceptable ↔ v.Takes c.complementizer) := by
  decide +kernel

theorem tam_rows :
    ∀ row ∈ Examples.all, ∀ c ∈ clauseTypeOf row, ∀ t ∈ row.feature? "embeddedTAM",
      t ≠ "none" → (row.judgment = .acceptable ↔ c.complementizer.IsFinite) := by
  decide +kernel

theorem focus_npi_rows :
    ∀ row ∈ Examples.all, ∀ c ∈ clauseTypeOf row,
      (row.feature? "diagnostic" = some "focus" →
        (row.judgment = .acceptable ↔ c.complementizer.IsFinite)) ∧
      (row.feature? "diagnostic" = some "npi" → row.feature? "negation" = some "matrix" →
        (row.judgment = .acceptable ↔ ¬ c.complementizer.IsFinite)) := by
  decide +kernel

theorem negation_rows :
    ∀ row ∈ Examples.all, ∀ c ∈ clauseTypeOf row, ∀ p ∈ row.feature? "negationPosition",
      (p = "preverbal" ↔ ¬ c.complementizer.IsFinite) := by
  decide +kernel

theorem subject_tone_rows :
    ∀ row ∈ Examples.all, row.judgment = .acceptable → ∀ c ∈ clauseTypeOf row,
      ∀ t ∈ row.feature? "subjectTone", (t = "high") = (c = .ni) := by
  decide +kernel

/-! ### The irrealis marker -/

theorem marker_rows :
    ∀ row ∈ Examples.all, row.feature? "clauseContext" ∈ [none, some "control"] →
      ∀ m ∈ row.feature? "irrealisMarker",
        (m = "present" ↔ (row.feature? "control").isSome) := by
  decide +kernel

-- [karttunen-1971]
theorem implicative_rows :
    ∀ row ∈ Examples.all, row.feature? "diagnostic" = some "implicative" →
      ∀ v ∈ verbOf row,
        (row.feature? "irrealisMarker" = some "absent" ↔
          v.implicative.positive = .some .positive) := by
  decide +kernel

/-! ### The OC signature (Table 2) -/

theorem cCommand_rows :
    ∀ row ∈ Examples.all, row.feature? "diagnostic" = some "cCommand" →
      (row.judgment = .acceptable ↔ row.feature? "antecedent" = some "cCommanding") := by
  decide +kernel

theorem longDistance_rows :
    ∀ row ∈ Examples.all, row.feature? "diagnostic" = some "longDistance" →
      (row.judgment = .acceptable ↔ row.feature? "antecedent" = some "local") := by
  decide +kernel

theorem sloppy_only :
    ∃ row ∈ Examples.all, row.feature? "diagnostic" = some "ellipsis" ∧
      ("sloppy", .acceptable) ∈ row.readings ∧ ("strict", .unacceptable) ∈ row.readings := by
  decide +kernel

theorem free_reading_rows :
    ∀ row ∈ Examples.all, ∀ c ∈ clauseTypeOf row, ∀ j, ("free", j) ∈ row.readings →
      (j = .acceptable ↔ c.complementizer.IsFinite) := by
  decide +kernel

theorem deSe_witness :
    ∃ row ∈ Examples.all, row.feature? "diagnostic" = some "deSe" ∧
      row.judgment = .unacceptable ∧ row.context ≠ "" := by
  decide +kernel

theorem controlled_form_covaries : table (.sg2, .subjective) ≠ table (.pl2, .subjective) := by
  decide

/-- The diagnostics the rows attest for a clause type. -/
def attested (c : EmbeddedClauseType) : Set Diagnostic :=
  {d | ∃ row ∈ Examples.all, clauseTypeOf row = some c ∧ Landau2013.attests row d}

instance (c : EmbeddedClauseType) : DecidablePred (· ∈ attested c) := fun d ↦ by
  unfold attested; infer_instance

/-- The control profile of a clause type in [landau-2013]'s signature, the clauses no attested
    diagnostic refutes. -/
def gaProfile (c : EmbeddedClauseType) : Set Landau2013.Clause74 :=
  ofAttested (attested c)

theorem attested_ni : attested .ni = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]; decide +kernel

theorem ni_obligatory : gaProfile .ni = Set.univ :=
  ofAttested_eq_univ_iff.2 attested_ni

theorem admits_ni : admits (gaProfile .ni) = ∅ := admits_eq_empty_iff.2 ni_obligatory

theorem arbitrary_mem_attested_ake : .arbitraryControl ∈ attested .ake := by
  decide +kernel

theorem ake_not_obligatory : gaProfile .ake ≠ Set.univ := fun h ↦
  Set.notMem_empty _ (ofAttested_eq_univ_iff.1 h ▸ arbitrary_mem_attested_ake)

/-! ### Landau's scale -/

/-- Gã clause types on [landau-2004]'s finiteness scale — a scale position, not
    a mood claim. Unrestricted TAM and independent tense both coincide with the
    complementizer's finiteness (exx 109–111, 118–119). -/
def gaToLandau (c : EmbeddedClauseType) : ClauseClass :=
  .ofFiniteness (decide c.complementizer.IsFinite) (decide c.complementizer.IsFinite)

theorem ga_no_fSubjunctive (c : EmbeddedClauseType) : gaToLandau c ≠ .fSubjunctive := by
  cases c <;> decide

theorem landau_predicts_control (c : EmbeddedClauseType) (hc : c ≠ .keji) (agr : Bool) :
    gaProfile c = Set.univ ↔ (gaToLandau c).HasOC agr := by
  cases c with
  | keji => exact absurd rfl hc
  | ni => exact iff_of_true ni_obligatory (by cases agr <;> decide)
  | ake => exact iff_of_false ake_not_obligatory (by cases agr <;> decide)

theorem not_isFinite_codings_iff (c : EmbeddedClauseType) :
    (∀ cd ∈ c.frame.codings, ¬ cd.IsFinite) ↔ ¬ c.complementizer.IsFinite := by
  cases c <;> decide

/-! ### Table 4 -/

/-- The five irrealis contexts of Table 4. -/
inductive IrrealisContext where
  | subjunctive
  | imperative
  | conditional
  | future
  | embeddedControl
  deriving DecidableEq, Repr

/-- The context a row's `clauseContext` names. -/
def contextOf : String → Option IrrealisContext
  | "subjunctive" => some .subjunctive
  | "imperative" => some .imperative
  | "conditional" => some .conditional
  | "future" => some .future
  | "control" => some .embeddedControl
  | _ => none

/-- The irrealis marker has three exponents, high tone on the subject, high tone on the verb,
    and the vowel segment *a*. -/
inductive Exponent where
  | subjectTone
  | verbTone
  | vowel
  deriving DecidableEq, Repr, Fintype

/-- A row shows an exponent. -/
def shows (row : Datum) : Exponent → Prop
  | .subjectTone => row.feature? "subjectTone" = some "high"
  | .verbTone => row.feature? "verbTone" = some "high"
  | .vowel => row.feature? "irrealisVowel" = some "present"

instance (row : Datum) : DecidablePred (shows row) := fun e ↦ by
  cases e <;> unfold shows <;> infer_instance

/-- The rows in an irrealis context with judgment `j`. -/
def rowsIn (ctx : IrrealisContext) (j : Judgment) : List Datum :=
  Examples.all.filter fun row ↦
    decide ((row.feature? "clauseContext").bind contextOf = some ctx ∧ row.judgment = j)

/-- Table 4 is read off the rows, as the exponents some grammatical row shows in the context
    (exx 85–86, 93–97, 100–103). -/
def realization (ctx : IrrealisContext) : Finset Exponent :=
  Finset.univ.filter fun e ↦ ∃ row ∈ rowsIn ctx .acceptable, shows row e

theorem realization_control : realization .embeddedControl = {.subjectTone} := by
  decide +kernel

theorem control_realization_unique (c : IrrealisContext) :
    realization c = realization .embeddedControl → c = .embeddedControl := by
  cases c <;> decide +kernel

theorem realization_exact :
    (∃ row ∈ rowsIn .embeddedControl .ungrammatical, shows row .verbTone) ∧
    (∃ row ∈ rowsIn .future .ungrammatical, shows row .subjectTone) ∧
    ∃ row ∈ rowsIn .subjunctive .ungrammatical, ¬ shows row .verbTone := by
  decide +kernel

/-! ### Deriving the overt pronoun -/

/-- A tonal exponent needs a segmental host; the null form has none. -/
def HostsTone (f : Form) : Prop := f ≠ .null

/-- The controlled-subject form must host the irrealis tone Table 4 places on
    the embedded-control subject. -/
def HostsControlTone (inv : Vocabulary Form) : Prop :=
  .subjectTone ∈ realization .embeddedControl → HostsTone inv.controlForm

theorem null_pro_impossible (inv : Vocabulary Form) (h : inv.controlForm = .null) :
    ¬ HostsControlTone inv := fun hc ↦
  hc (realization_control ▸ Finset.mem_singleton_self _) h

theorem ga_hostsControlTone : HostsControlTone gaInventory := fun _ h ↦ nomatch h

theorem ga_overt_pro : gaInventory.controlForm = .pronoun := rfl

end Allotey2021
