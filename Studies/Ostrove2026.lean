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

/-- The fragment's controlled complements are exactly its untensed subjunctives: no finite
complement is controlled, not even that of *kònì* 'know', which also takes an untensed one. -/
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

/-- By the tense column, only untensed subjunctives lack a tense of their own. -/
theorem independentTense_iff (c : EmbeddedClauseType) :
    IndependentTense c ↔ c ≠ .untensedSubjunctive := by
  cases c <;> decide +kernel

/-- The restructuring column holds of the rows except under *kòni* 'want', out of whose tensed
subjunctive a quantifier fronts (fn. 8), so the rows make tensed subjunctives restructure too. -/
theorem restructures_iff (c : EmbeddedClauseType) : Restructures c ↔ c ≠ .finite := by
  cases c <;> decide +kernel

/-- With its exception, the restructuring column says that a quantifier fronts out of an
embedded clause exactly when the clause is an untensed subjunctive or the verb is *kòni* 'want'
((20), (22), (24), (109)). -/
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

/-- No row attests a criterial configuration of an untensed subjunctive, and every other clause
type attests one: free subjects (12), (18), strict ellipsis (30), (32), and non-c-commanding
antecedents (43), (45) against (19), (33), (44), (46). -/
theorem attested_eq_empty_iff (c : EmbeddedClauseType) :
    attested c = ∅ ↔ c = .untensedSubjunctive := by
  rw [Set.eq_empty_iff_forall_notMem]
  cases c <;> decide +kernel

/-- The control profile of a clause type in [landau-2013]'s signature, the clauses no attested
diagnostic refutes. -/
def smpmProfile (c : EmbeddedClauseType) : Set Landau2013.Clause74 :=
  ofAttested (attested c)

/-- Only untensed subjunctives are obligatory-control clauses. -/
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

/-- SMPM realizes every position of the scale, unlike Gã (`Allotey2021.ga_no_fSubjunctive`). -/
theorem smpmToLandau_landauToSMPM (c : ClauseClass) : smpmToLandau (landauToSMPM c) = c := by
  cases c <;> decide +kernel

/-- Landau's calculus predicts the control profile of every clause type exactly when the clauses
are `[+Agr]`: at `[−Agr]` it makes the tensed subjunctive, an F-subjunctive, obligatory control,
yet its subject may be disjoint from the matrix subject (18b). -/
theorem landau_predicts_control_iff (agr : Bool) :
    (∀ c, smpmProfile c = Set.univ ↔ (smpmToLandau c).HasOC agr) ↔ agr = true := by
  simp only [isObligatory_iff]
  cases agr <;> decide +kernel

/-! ### Against movement (§6) -/

/-- An exempt anaphor with a quantified antecedent is out in a simple clause (75) and good inside
an untensed subjunctive under a quantified controller ((86), (87)). -/
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

/-- Exempt anaphors reject quantified antecedents (78) yet are available in untensed
subjunctives under quantified controllers (`exemptAnaphor_rows`), so the embedded position holds
a referential pronoun and not a copy of the quantifier: the dependency is not movement. -/
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

/-- PRO is overt in SMPM, since no SMPM item is conditioned on the controlled subject, so it
takes the elsewhere pronoun (98), where English's null item yields silent PRO (94a). -/
theorem smpm_overt_pro :
    smpmInventory.controlForm = smpmInventory.elsewhere ∧ englishInventory.controlForm = .null :=
  ⟨Vocabulary.realize_eq_elsewhere (by decide), rfl⟩

/-- In general form, with the pronoun as its elsewhere form a language has silent PRO only
through a null item for controlled subjects, which SMPM lacks. -/
theorem smpm_no_null_item : ∀ i ∈ smpmInventory.items, i.exponent ≠ .null := by decide

/-- In the syncretism table (92), each row derived from its inventory, a cell is a context in
which the bound form is the referential pronoun's, whose own column is the elsewhere form itself.
The four languages occupy four distinct cells. -/
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

/-- The pronouns that can be a controlled subject are exactly the clitics, none of which bears
focus (65), (66): the overt subject is not the focused pronoun of scope-sensitive copy
control. -/
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

/-- SMPM instantiates the universal: overt PRO and no pro-drop. -/
theorem smpm_universal54 : Universal54 smpmInventory pronominalSubjects := fun _ ↦ rfl

/-- English satisfies it vacuously, whatever its 101A cell, since its PRO is null. -/
theorem english_universal54 (s : Data.WALS.F101A.ExpressionOfPronominalSubjects) :
    Universal54 englishInventory s :=
  fun h ↦ absurd rfl h

/-- Gã sits in SMPM's cell: the same controlled-subject realization, derived from the Gã
inventory of [allotey-2021], and the same 101A cell. -/
theorem ga_patterns_with_smpm :
    Allotey2021.gaInventory.controlForm = smpmInventory.controlForm ∧
      Allotey2021.pronominalSubjects = pronominalSubjects :=
  ⟨rfl, rfl⟩

/-- Gã instantiates the universal ([allotey-2021]). -/
theorem ga_universal54 : Universal54 Allotey2021.gaInventory Allotey2021.pronominalSubjects :=
  fun _ ↦ rfl

/-- The universal has bite for Gã: under [wals-2013]'s coding of its subject markers as affixes
(`Allotey2021.wals_codes_affixes`) Gã violates it, so its instance rests on [allotey-2021]'s
analysis of the markers as pronouns. -/
theorem ga_violates_universal54_of_wals :
    ∀ s ∈ Data.WALS.F101A.allData.lookup "ga",
      ¬ Universal54 Allotey2021.gaInventory s := by
  intro s hs h
  rw [Allotey2021.wals_codes_affixes, Option.mem_some_iff] at hs
  subst hs
  exact absurd (h (by rw [Allotey2021.ga_overt_pro]; decide)) (by decide)

end Ostrove2026
