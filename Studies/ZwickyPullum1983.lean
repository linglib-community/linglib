module

public import Linglib.Morphology.Morph
public import Linglib.Fragments.English.Auxiliaries
public import Linglib.Logic.Modal.Basic
public import Mathlib.Data.Fin.Basic

/-!
# Zwicky and Pullum (1983): Cliticization vs. Inflection: English n't

This file formalizes Zwicky and Pullum's six criteria for telling clitics from
inflectional affixes and their application to the English contracted negator *-n't*. Clitics
show a low degree of selection with respect to their hosts, no arbitrary gaps, no
morphophonological or semantic idiosyncrasies, are not affected by syntactic rules, and can
attach to material already containing clitics; affixes show the opposite on each count
(criteria A–F). A morpheme's profile on the six criteria (`CliticAffixProfile`) determines its
status (`CliticAffixProfile.classify`): the English contracted auxiliaries *'s*, *'ve* and *'d*
are clitic-like on every criterion and classify as simple clitics, the affixes *-ed*, *-s* and
*-est* are affix-like on every criterion, and *-n't*, taken almost without exception to be a
clitic, is affix-like on every criterion and classifies as an inflectional affix (`nt_is_affix`).
Two of the criteria are checked against the fragment of English auxiliaries: the paradigm gaps
*mayn't* and *amn't* of criterion B (`may_gap`, `am_gap`) and the irregular forms *won't*,
*can't*, *shan't*, *don't* and *mustn't* of criterion C (`irregularNegatives`). The semantic
idiosyncrasy of criterion D, that *can't* means `NOT(CAN(P))` while *mustn't* means
`MUST(NOT(P))`, is recorded as opposite scope patterns (`scope_idiosyncrasy`), and the two
scopings are separated on a Kripke model (`neg_over_poss_ne_poss_over_neg`,
`neg_over_nec_ne_nec_over_neg`).

## Implementation notes

* The classification takes the paper's two unanimous poles as decisive: six affix-like answers
  make an inflectional affix, six clitic-like answers a simple clitic. The paper defines special
  clitics distributionally, not as an intermediate score; the middle branch is a default.
* The criteria of a profile are Boolean data read off the paper's discussion; only the two
  fragment-checked criteria are derived.

## References

* [zwicky-pullum-1983]
-/

@[expose] public section

namespace Morphology.Diagnostics

/-! ### The six criteria -/

/-- The degree of selection of a bound morpheme with respect to its hosts, criterion A. -/
inductive SelectionDegree
  /-- Words of virtually any category, as for the contracted auxiliaries. -/
  | low
  /-- Words of one major category, as for the past tense *-ed*. -/
  | singleCategory
  /-- A closed list of stems, as for *-n't* on the finite auxiliaries. -/
  | closedClass
  deriving DecidableEq, Repr

/-- Affixes are more selective than clitics. -/
def SelectionDegree.IsHighSelection (s : SelectionDegree) : Prop := s ≠ .low

instance : DecidablePred SelectionDegree.IsHighSelection := fun s ↦
  inferInstanceAs (Decidable (s ≠ .low))

/-- The status of a bound form on the word, clitic, affix cline. -/
inductive MorphStatus
  /-- A syntactically independent word. -/
  | freeWord
  /-- A simple clitic, an optional variant of a full form in the full form's positions. -/
  | simpleClitic
  /-- A special clitic, without a corresponding full form or with a distribution of its own. -/
  | specialClitic
  /-- An inflectional affix. -/
  | inflAffix
  /-- A derivational affix. -/
  | derivAffix
  deriving DecidableEq, Repr

/-- An inflectional or derivational affix. -/
def MorphStatus.IsAffix (s : MorphStatus) : Prop := s = .inflAffix ∨ s = .derivAffix

instance : DecidablePred MorphStatus.IsAffix := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- A simple or special clitic. -/
def MorphStatus.IsClitic (s : MorphStatus) : Prop := s = .simpleClitic ∨ s = .specialClitic

instance : DecidablePred MorphStatus.IsClitic := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- A morpheme's answers to the six criteria. -/
structure CliticAffixProfile where
  /-- Criterion A. -/
  selection : SelectionDegree
  /-- Criterion B: arbitrary gaps in the set of combinations. -/
  hasArbitraryGaps : Bool
  /-- Criterion C: morphophonological idiosyncrasies of the combinations. -/
  hasMorphophonIdiosyncrasies : Bool
  /-- Criterion D: semantic idiosyncrasies of the combinations. -/
  hasSemanticIdiosyncrasies : Bool
  /-- Criterion E: syntactic rules affect the combinations. -/
  syntacticRulesApply : Bool
  /-- Criterion F: the morpheme attaches to material already containing clitics. -/
  attachesToCliticizedMaterial : Bool
  deriving DecidableEq, Repr

namespace CliticAffixProfile

variable (p : CliticAffixProfile)

/-- The number of criteria on which the profile is affix-like. -/
def affixScore : ℕ :=
  [decide p.selection.IsHighSelection, p.hasArbitraryGaps, p.hasMorphophonIdiosyncrasies,
    p.hasSemanticIdiosyncrasies, p.syntacticRulesApply,
    !p.attachesToCliticizedMaterial].count true

/-- The number of criteria on which the profile is clitic-like. -/
def cliticScore : ℕ := 6 - p.affixScore

/-- The status a profile determines: affix-like on every criterion is an inflectional affix,
clitic-like on every criterion a simple clitic. -/
def classify : MorphStatus :=
  if p.affixScore = 6 then .inflAffix
  else if p.cliticScore = 6 then .simpleClitic
  else .specialClitic

theorem classify_of_affixScore_eq_six (h : p.affixScore = 6) : p.classify = .inflAffix := by
  simp [classify, h]

theorem classify_of_affixScore_eq_zero (h : p.affixScore = 0) : p.classify = .simpleClitic := by
  simp [classify, h, cliticScore]

end CliticAffixProfile

end Morphology.Diagnostics

namespace ZwickyPullum1983

open Morphology.Diagnostics

/-! ### The profiles -/

/-- The contracted auxiliary *'s*: clitic-like on every criterion. -/
def cliticS : CliticAffixProfile where
  selection := .low
  hasArbitraryGaps := false
  hasMorphophonIdiosyncrasies := false
  hasSemanticIdiosyncrasies := false
  syntacticRulesApply := false
  attachesToCliticizedMaterial := true

/-- The contracted auxiliary *'ve*. -/
def cliticVe : CliticAffixProfile := cliticS

/-- The contracted auxiliary *'d*. -/
def cliticD : CliticAffixProfile := cliticS

/-- The past tense *-ed*: affix-like on every criterion. -/
def affixEd : CliticAffixProfile where
  selection := .singleCategory
  hasArbitraryGaps := true
  hasMorphophonIdiosyncrasies := true
  hasSemanticIdiosyncrasies := true
  syntacticRulesApply := true
  attachesToCliticizedMaterial := false

/-- The plural *-s*. -/
def affixPluralS : CliticAffixProfile := affixEd

/-- The superlative *-est*. -/
def affixEst : CliticAffixProfile := affixEd

/-- The contracted negator *-n't*: selective for the finite auxiliaries, with the gaps
*mayn't* and *amn't*, the irregular *won't* and *can't*, the scope idiosyncrasy of *mustn't*
against *can't*, subject to inversion, and unable to attach to *I'd*. -/
def negNt : CliticAffixProfile where
  selection := .closedClass
  hasArbitraryGaps := true
  hasMorphophonIdiosyncrasies := true
  hasSemanticIdiosyncrasies := true
  syntacticRulesApply := true
  attachesToCliticizedMaterial := false

theorem cliticS_is_clitic : cliticS.classify = .simpleClitic := by decide

theorem affixEd_is_affix : affixEd.classify = .inflAffix := by decide

/-- *-n't* is an inflectional affix, not a clitic. -/
theorem nt_is_affix : negNt.classify = .inflAffix := by decide

/-- *-n't* is affix-like on all six criteria. -/
theorem nt_affixScore : negNt.affixScore = 6 := by decide

/-! ### Criteria B and C on the fragment -/

open English.Auxiliaries

/-- *mayn't* is a paradigm gap. -/
theorem may_gap : negative may = none := by decide

/-- *amn't* is a paradigm gap. -/
theorem am_gap : negative am = none := by decide

/-- The contracted negatives whose form is not the auxiliary with *-n't* suffixed: *won't*,
*can't*, *shan't*, *don't* and *mustn't*. -/
def irregularNegatives : List Auxiliary := [wont, cant, shant, dont, mustnt]

theorem irregular_are_negatives : ∀ a ∈ irregularNegatives, a ∈ negatives := by decide

/-! ### Criterion D: the scope of the contracted negator -/

open Modality (ModalForce)
open ModalLogic (Box Diamond)

/-- The scope of negation relative to the modal in a contracted negative. -/
inductive NegModalScope
  /-- `NOT(MODAL(P))`, as in *you can't go*. -/
  | negOverModal
  /-- `MODAL(NOT(P))`, as in *you mustn't go*. -/
  | modalOverNeg
  deriving DecidableEq, Repr

/-- The modal force and the scope reading a contracted negative selects. -/
structure ContractedNegScope where
  force : ModalForce
  scope : NegModalScope
  deriving DecidableEq, Repr

/-- *can't* denies the possibility. -/
def cantScope : ContractedNegScope := ⟨.possibility, .negOverModal⟩

/-- *mustn't* requires the negation. -/
def mustntScope : ContractedNegScope := ⟨.necessity, .modalOverNeg⟩

/-- The two contracted forms select opposite scopes, the irregularity in the connection between
the contracted and the uncontracted form. -/
theorem scope_idiosyncrasy : cantScope.scope ≠ mustntScope.scope := by decide

/-- A four-world frame on which the actual world sees two worlds and every other world only
itself. -/
private def kripkeR : SetRel (Fin 4) (Fin 4) :=
  .ofSuccessors fun w ↦
    match w with
    | 0 => {1, 2}
    | 1 => {1}
    | 2 => {2}
    | 3 => {3}

/-- A proposition true at the first two worlds and false at the others. -/
private def witnessP : Fin 4 → Prop := fun w ↦
  match w with
  | 0 | 1 => True
  | 2 | 3 => False

private instance : DecidablePred witnessP := fun w ↦ by
  unfold witnessP
  match w with
  | 0 | 1 | 2 | 3 => infer_instance

/-- `NOT(CAN(P))` and `CAN(NOT(P))` come apart: on the frame, both `P` and `¬P` are possible at
the actual world. -/
theorem neg_over_poss_ne_poss_over_neg :
    ∃ R : SetRel (Fin 4) (Fin 4),
      ¬ ∀ (p : Fin 4 → Prop) (w : Fin 4), ¬ Diamond R p w ↔ Diamond R (fun w' ↦ ¬ p w') w := by
  refine ⟨kripkeR, fun h ↦ ?_⟩
  have := h witnessP 0
  simp [Diamond, kripkeR, witnessP] at this

/-- `NOT(MUST(P))` and `MUST(NOT(P))` come apart: on the frame, `P` is not necessary at the
actual world, yet not necessarily false either. -/
theorem neg_over_nec_ne_nec_over_neg :
    ∃ R : SetRel (Fin 4) (Fin 4),
      ¬ ∀ (p : Fin 4 → Prop) (w : Fin 4), ¬ Box R p w ↔ Box R (fun w' ↦ ¬ p w') w := by
  refine ⟨kripkeR, fun h ↦ ?_⟩
  have := h witnessP 0
  simp [Box, kripkeR, witnessP] at this

end ZwickyPullum1983
