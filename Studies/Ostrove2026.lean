module

public import Linglib.Syntax.Binding.MinimalPronoun
public import Linglib.Fragments.Mixtec.SMPM.Pronouns
public import Linglib.Fragments.Mixtec.SMPM.Verbs
public import Linglib.Syntax.Control.Head
public import Linglib.Syntax.Control.Basic
public import Linglib.Syntax.Control.Diagnostics
public import Studies.Landau2013
public import Studies.Allotey2021
public import Linglib.Data.Examples.Ostrove2026

/-!
# Ostrove (2026): Obligatorily Overt PRO in San Martín Peras Mixtec

Ostrove argues that San Martín Peras Mixtec (SMPM) has obligatory control whose controlled subject
must be an overt clitic pronoun. Its three embedded clause types, finite clauses, tensed
subjunctives and untensed subjunctives, are told apart by aspect, tense and restructuring
(`unrestrictedTAM_iff`, `independentTense_iff`, `frontingOut_iff`), and only the untensed
subjunctive shows Landau's signature of obligatory control (`isObligatory_iff`). Exempt anaphors
reject quantified antecedents yet occur in untensed subjunctives under quantified controllers, so
the controlled subject is a pronoun rather than a copy left by movement (`smpm_refutes_movement`).
The analysis is morphological: bound variables are minimal pronouns realized by vocabulary items,
and SMPM lacks the null item that yields silent PRO elsewhere, so the elsewhere pronoun surfaces
(`smpm_overt_pro`, `syncretism_typology`). A tentative universal closes the argument: overt PRO
entails no pro-drop (`Universal54`).

## Implementation notes

The properties of (26) and the control profile are read off the paper's example rows
(`Data/Examples/Ostrove2026.json`), whose clause types agree with the fragment's verbs
(`clauseTypeOf_mem_verbOf`). The rows bear out (26) except in its restructuring column, which
footnote 8's exception under *kòni* 'want' breaks (`restructures_iff`). The paper's examples of
non-exhaustive binding in tensed subjunctives are a missing cross-reference in the manuscript, so
partial control is attested only as absent from untensed subjunctives. Landau's calculus fits the
three types only if the tensed subjunctive is `[+Agr]` (`landau_predicts_control_iff`), which the
paper does not discuss. The pro-drop status is the paper's own 101A cell, as WALS does not sample
the language. Example numbers follow the manuscript version of the article.

## References

* [ostrove-2026]
* [landau-2004]
* [landau-2015]
* [kratzer-2009]
* [safir-2014]
* [cardinaletti-starke-1999]
* [polinsky-potsdam-2006]
* [allotey-2021]
* [wals-2013]
* [sulemana-2021]
* [black-1994]
* [dechaine-manfredi-1994]
-/

@[expose] public section

namespace Ostrove2026

open Binding.MinimalPronoun
open scoped DistributedMorphology
open Control
open Mixtec.SMPM

/-! ### The clause typology (26) -/

/-- The three embedded clause types of (26). -/
inductive EmbeddedClauseType where
  | finite
  | tensedSubjunctive
  | untensedSubjunctive
  deriving DecidableEq, Repr, Fintype

/-- A verb's complement in a diathesis is finite in the indicative coding and otherwise a
subjunctive, untensed exactly when a participant of the diathesis controls it (§3). -/
def EmbeddedClauseType.ofDiathesis {n : ℕ} (d : Diathesis n) : EmbeddedClauseType :=
  if Clause.ComplementType.indicative ∈ d.codings then .finite
  else if d.controller.isSome then .untensedSubjunctive
  else .tensedSubjunctive

theorem control_iff_untensed : ∀ v ∈ verbs, ∀ d ∈ v.valency.diatheses,
    d.controller.isSome ↔ EmbeddedClauseType.ofDiathesis d = .untensedSubjunctive := by
  decide

/-! ### The rows -/

/-- The clause type a row's `clauseType` feature names. -/
def clauseTypeOf (row : Datum) : Option EmbeddedClauseType :=
  match row.feature? "clauseType" with
  | some "finite" => some .finite
  | some "tensedSubjunctive" => some .tensedSubjunctive
  | some "untensedSubjunctive" => some .untensedSubjunctive
  | _ => none

/-- The fragment verb a row's `verb` feature names. -/
def verbOf (row : Datum) : Option Verb :=
  (row.feature? "verb").bind (Verb.find? verbs ·)

/-- The rows agree with the predicate lists (27): each row's clause type is one its matrix verb
takes in the fragment. -/
theorem clauseTypeOf_mem_verbOf : ∀ row ∈ Examples.all, ∀ c ∈ clauseTypeOf row,
    ∃ v ∈ verbOf row, ∃ d ∈ v.valency.diatheses, EmbeddedClauseType.ofDiathesis d = c := by
  decide +kernel


/-! ### The clause typology (26) from the rows -/

/-- A clause type has unrestricted TAM when it has an acceptable row in each of the three
aspects ((9), (13)). -/
def UnrestrictedTAM (c : EmbeddedClauseType) : Prop :=
  ∀ a ∈ ["completive", "continuous", "irrealis"], ∃ row ∈ Examples.all,
    clauseTypeOf row = some c ∧ row.feature? "aspect" = some a ∧ row.judgment = .acceptable

instance (c : EmbeddedClauseType) : Decidable (UnrestrictedTAM c) := by
  unfold UnrestrictedTAM; infer_instance

/-- A clause type has a tense of its own when an acceptable row gives it a time adverb the matrix
clause does not share ((10), (16), (17)). -/
def IndependentTense (c : EmbeddedClauseType) : Prop :=
  ∃ row ∈ Examples.all, clauseTypeOf row = some c ∧ row.feature? "diagnostic" = some "tense" ∧
    row.judgment = .acceptable

instance (c : EmbeddedClauseType) : Decidable (IndependentTense c) := by
  unfold IndependentTense; infer_instance

/-- A clause type restructures when an acceptable row fronts a quantifier out of it into the
matrix clause ((20), (22), (24)). -/
def Restructures (c : EmbeddedClauseType) : Prop :=
  ∃ row ∈ Examples.all, clauseTypeOf row = some c ∧ row.feature? "fronting" = some "out" ∧
    row.judgment = .acceptable

instance (c : EmbeddedClauseType) : Decidable (Restructures c) := by
  unfold Restructures; infer_instance

/-- By the TAM column of (26), only finite clauses take every aspect. -/
theorem unrestrictedTAM_iff (c : EmbeddedClauseType) : UnrestrictedTAM c ↔ c = .finite := by
  cases c <;> decide +kernel

theorem independentTense_iff (c : EmbeddedClauseType) :
    IndependentTense c ↔ c ≠ .untensedSubjunctive := by
  cases c <;> decide +kernel

/-- An embedded clause type restructures iff it is not finite, tensed subjunctives included (fn. 8).
-/
theorem restructures_iff (c : EmbeddedClauseType) : Restructures c ↔ c ≠ .finite := by
  cases c <;> decide +kernel

/-- A quantifier fronts out of an embedded clause iff the clause is an untensed subjunctive or the
verb is *kòni* 'want' ((20), (22), (24), (109)). -/
theorem frontingOut_iff : ∀ row ∈ Examples.all, row.feature? "fronting" = some "out" →
    (row.judgment = .acceptable ↔
      clauseTypeOf row = some .untensedSubjunctive ∨ row.feature? "verb" = some "kòni") := by
  decide +kernel

/-! ### Obligatory control (§4) -/

/-- The diagnostics the rows attest for a clause type. The paper tests neither long-distance
antecedents nor readings under *only*. -/
def attested (c : EmbeddedClauseType) : Set Diagnostic :=
  {d | ∃ row ∈ Examples.all, clauseTypeOf row = some c ∧ Landau2013.attests row d}

instance (c : EmbeddedClauseType) : DecidablePred (· ∈ attested c) := fun d ↦ by
  unfold attested; infer_instance

/-- Only the untensed subjunctive attests no free subject (12), (18), strict ellipsis (30), (32) or
non-c-commanding antecedent (43), (45), against (19), (33), (44), (46). -/
theorem attested_eq_empty_iff (c : EmbeddedClauseType) :
    attested c = ∅ ↔ c = .untensedSubjunctive := by
  rw [Set.eq_empty_iff_forall_notMem]
  cases c <;> decide +kernel

/-- The control profile of a clause type in [landau-2013]'s signature, the clauses no attested
diagnostic refutes. -/
def smpmProfile (c : EmbeddedClauseType) : Set Landau2013.Clause74 :=
  ofAttested (attested c)

theorem isObligatory_iff (c : EmbeddedClauseType) :
    smpmProfile c = Set.univ ↔ c = .untensedSubjunctive := by
  rw [smpmProfile, ofAttested_eq_univ_iff, attested_eq_empty_iff]

/-- Untensed subjunctives reject partial control (37). -/
theorem partialControl_rows : ∀ row ∈ Examples.all,
    row.feature? "diagnostic" = some "partialControl" →
      clauseTypeOf row = some .untensedSubjunctive ∧ row.judgment = .ungrammatical := by
  decide +kernel

/-! ### Landau's scale -/

/-- The clause types on the finiteness scale of [landau-2004], untensed subjunctives being
C-subjunctives and tensed ones F-subjunctives (§3). -/
def landauToSMPM : ClauseClass → EmbeddedClauseType
  | .cSubjunctive => .untensedSubjunctive
  | .fSubjunctive => .tensedSubjunctive
  | .finite => .finite

/-- The scale position of a clause type, from its TAM and tense properties. -/
def smpmToLandau (c : EmbeddedClauseType) : ClauseClass :=
  .ofFiniteness (decide (UnrestrictedTAM c)) (decide (IndependentTense c))

theorem smpmToLandau_landauToSMPM (c : ClauseClass) : smpmToLandau (landauToSMPM c) = c := by
  cases c <;> decide +kernel

/-- Landau's calculus predicts every clause type's control profile iff the clauses are `[+Agr]`,
failing at `[−Agr]` on the tensed subjunctive (18b). -/
theorem landau_predicts_control_iff (agr : Bool) :
    (∀ c, smpmProfile c = Set.univ ↔ (smpmToLandau c).HasOC agr) ↔ agr = true := by
  simp only [isObligatory_iff]
  cases agr <;> decide +kernel

/-! ### Against movement (§6) -/

/-- Exempt anaphors reject quantified antecedents in simple clauses (75) but accept quantified
controllers of untensed subjunctives ((86), (87)). -/
theorem exemptAnaphor_rows : ∀ row ∈ Examples.all,
    row.feature? "diagnostic" = some "exemptAnaphor" →
      (row.judgment = .acceptable ↔ clauseTypeOf row = some .untensedSubjunctive) := by
  decide +kernel

/-- The occupants of the configurations (86) and (87), a quantified controller and the overt
controlled clitic that antecedes an exempt anaphor. -/
inductive Ex86Item where
  | quantifierDP
  | pronoun
  deriving DecidableEq

/-- The control dependency of (86) and (87), from the controller position to the embedded
clitic position. -/
def ex86Dependency : SetRel (Fin 2) (Fin 2) := {(0, 1)}

/-- The attested occupants of the two positions. -/
def ex86Occupant : Fin 2 → Ex86Item := fun p ↦ if p = 0 then .quantifierDP else .pronoun

/-- The controlled dependency in an untensed subjunctive is not movement, its subject being a
referential pronoun (78). -/
theorem smpm_refutes_movement : ¬ IsExhaustive ex86Occupant ex86Dependency :=
  not_isExhaustive_of_mismatch (P := (· = .quantifierDP)) rfl rfl (by decide)

/-! ### Minimal pronoun inventories (§7) -/

/-- The English inventory (94), with a null item for controlled subjects, a reflexive for local
binding, and the pronoun elsewhere. -/
def englishInventory : Vocabulary Form where
  items := [{.controlledSubject} ⟷ .null, {.locallyBound} ⟷ .reflexive]
  elsewhere := .pronoun

/-- The Haitian Creole inventory (96), with a null item for controlled subjects and no reflexive
item, reflexives surfacing as pronouns ([dechaine-manfredi-1994]). -/
def haitianInventory : Vocabulary Form where
  items := [{.controlledSubject} ⟷ .null]
  elsewhere := .pronoun

/-- The SMPM inventory (98), with a reflexive item, *mí* with a clitic, and no null item. -/
def smpmInventory : Vocabulary Form where
  items := [{.locallyBound} ⟷ .reflexive]
  elsewhere := .pronoun

/-- The Quiegolani Zapotec inventory ([black-1994]), with no context-specific item at all. -/
def quiegolaniInventory : Vocabulary Form where
  items := []
  elsewhere := .pronoun

/-- PRO is overt in SMPM, the elsewhere pronoun (98), while English's null item makes PRO silent
(94a). -/
theorem smpm_overt_pro :
    smpmInventory.controlForm = smpmInventory.elsewhere ∧ englishInventory.controlForm = .null :=
  ⟨Vocabulary.realize_eq_elsewhere (by decide), rfl⟩

theorem smpm_no_null_item : ∀ i ∈ smpmInventory.items, i.exponent ≠ .null := by decide

/-- The four languages occupy four distinct cells of the syncretism table (92), each derived from
its inventory. -/
theorem syncretism_typology :
    englishInventory.syncretic = {.boundVariable} ∧
      quiegolaniInventory.syncretic = Finset.univ ∧
      haitianInventory.syncretic = {.locallyBound, .boundVariable} ∧
      smpmInventory.syncretic = {.controlledSubject, .boundVariable} := by
  decide

/-! ### Copy control (§5) -/

/-- The four types of copy control, an overt element in the controlled position
([polinsky-potsdam-2006]), a full copy of the controller, or a pronoun that is overt in
attitude reports only, under scope-taking operators only, or unconditionally. -/
inductive CopyControlType where
  /-- San Lucas Quiaviní Zapotec, Copala Triqui. -/
  | fullCopy
  /-- Gengbe, Mandarin. -/
  | logophoricPronominal
  /-- Italian, Hungarian, European Portuguese, alternating with null PRO (60). -/
  | scopeSensitivePronominal
  /-- SMPM, Gã ([allotey-2021]), Bùlì ([sulemana-2021]). -/
  | obligatoryPronominal
  deriving DecidableEq

/-- SMPM's type, whose controlled subject is a pronoun rather than a full copy (57), overt
outside attitude reports, and unable to bear focus, so the scope-sensitive alternation with
null PRO is unavailable. -/
def smpmCopyControlType : CopyControlType := .obligatoryPronominal

/-- A non-clitic embedded subject, a clitic strengthened by the article or a demonstrative, is out
exactly in untensed subjunctives ((67), (68)). -/
theorem nonclitic_rows : ∀ row ∈ Examples.all,
    row.feature? "embeddedSubject" = some "nonclitic" →
      (row.judgment = .acceptable ↔ clauseTypeOf row = some .tensedSubjunctive) := by
  decide +kernel

/-- A controlled subject is of the clitic class of [cardinaletti-starke-1999], since non-clitic
forms are ungrammatical there (`nonclitic_rows`). -/
def controlledSubjectStrength : Pronoun.Strength := .clitic

/-- The pronouns that can be controlled subjects are exactly the clitics, none of which bears focus
(65), (66). -/
theorem controlledSubject_iff_mem_clitics :
    ∀ p ∈ pronouns, p.strength = some controlledSubjectStrength ↔ p ∈ clitics := by
  decide

/-! ### The implicational universal (54) -/

/-- SMPM's cell of [wals-2013]'s 101A, which does not sample the language, is obligatory
subject pronouns, expletive and impersonal ones included (3). -/
def pronominalSubjects : Data.WALS.F101A.ExpressionOfPronominalSubjects :=
  .obligatoryPronounsInSubjectPosition

/-- A language with minimal-pronoun inventory `inv` and 101A cell `s` satisfies the
implicational universal (54) when overt PRO implies obligatory subject pronouns, that is, no
pro-drop. -/
def Universal54 (inv : Vocabulary Form)
    (s : Data.WALS.F101A.ExpressionOfPronominalSubjects) : Prop :=
  inv.controlForm ≠ .null → s = .obligatoryPronounsInSubjectPosition

theorem smpm_universal54 : Universal54 smpmInventory pronominalSubjects := fun _ ↦ rfl

theorem english_universal54 (s : Data.WALS.F101A.ExpressionOfPronominalSubjects) :
    Universal54 englishInventory s :=
  fun h ↦ absurd rfl h

theorem ga_patterns_with_smpm :
    Allotey2021.gaInventory.controlForm = smpmInventory.controlForm ∧
      Allotey2021.pronominalSubjects = pronominalSubjects :=
  ⟨rfl, rfl⟩

theorem ga_universal54 : Universal54 Allotey2021.gaInventory Allotey2021.pronominalSubjects :=
  fun _ ↦ rfl

theorem ga_violates_universal54_of_wals :
    ∀ s ∈ Data.WALS.F101A.allData.lookup "ga",
      ¬ Universal54 Allotey2021.gaInventory s := by
  intro s hs h
  rw [Allotey2021.wals_codes_affixes, Option.mem_some_iff] at hs
  subst hs
  exact absurd (h (by rw [Allotey2021.ga_overt_pro]; decide)) (by decide)

end Ostrove2026
