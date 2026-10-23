module

public import Linglib.Morphology.Paradigm.Function
public import Mathlib.Tactic.DeriveFintype

/-!
# Stump (2016): Inflectional Paradigms

This file formalizes two of the deviations from the canonical content-to-form isomorphism
argued for in [stump-2016], on the paradigm-linkage model of the substrate's
`Morphology.Linkage`. Latin deponent verbs inflect by means of the morphology that
ordinarily expresses a verb's passive forms: the deponent *cōnārī* realizes its active
content cells with the passive personal endings a regular verb like *parāre* uses only for
its passive, and lacks passive-meaning forms. This is a property mapping that crosses the
voice axis: the regular verb's linkage preserves the content cell's property set and is
canonical (`parareLinkage_isCanonical`), while the deponent's replaces active with passive
on every active cell (`conari_deviates_on_every_active_cell`,
`conari_active_realized_by_passive_form`), so that the same active content cell has an
active form correspondent for the one verb and a passive one for the other
(`depon_vs_regular`).

The Kashmiri recent, indefinite and remote preterites of the intransitive conjugations II
and III are realized through four morphomic properties, the past morphomes a to d, by
property mappings that differ by one morphome (`pmII`, `pmIII`): the indefinite past of
WUP and the recent past of WUPH share the past b form correspondent and inflect alike
(`kashmiri_inflect_alike`), as do the remote past of WUP and the indefinite past of WUPH
(`kashmiri_inflect_alike_pastC`). Content cells carry the tenses and form cells the morphomes,
and within one conjugation the preterites keep distinct form correspondents
(`linkII_not_syncretic`). The form cells are realized by the PFM block cascade of
`Morphology.Paradigm.Function`.

## Implementation notes

The Latin cells are abstracted to voice and agreement, with the inflection-class index and
tense, aspect and mood held constant, and no realizations are attached to the Latin
linkages. The Kashmiri forms and their stem-plus-suffix segmentation are the book's
display of Grierson's paradigms, with the first person singular masculine exponents only. The
Kashmiri property mappings act property by property, which agrees with the book's mappings on
every property set with a single tense.

## References

* [stump-2016]
-/

@[expose] public section

namespace Stump2016

open Morphology

/-- Voice is the axis that Latin deponency crosses ([stump-2016] §12.1). -/
inductive Voice where
  | active
  | passive
  deriving DecidableEq, Repr

/-- `Agr` lists the six person–number cells of the imperfective present
indicative ([stump-2016] Tables 12.1–12.2). -/
inductive Agr where
  | s1 | s2 | s3 | p1 | p2 | p3
  deriving DecidableEq, Repr

/-- A cell is a morphosyntactic property set abstracted to the voice axis and the
agreement features relevant to Latin deponency (the inflection-class index and
tense/aspect/mood, held constant across the paradigm below, are elided). -/
structure Cell where
  agr : Agr
  voice : Voice
  deriving DecidableEq, Repr

/-- `LatinVerb` has the two Latin lexemes contrasted, the deponent *cōnārī* and the regular
*parāre*. -/
inductive LatinVerb where
  | conari
  | parare
  deriving DecidableEq, Repr

/-- `LatinStem` has one stem for each of the two verbs. -/
inductive LatinStem where
  | cona
  | para
  deriving DecidableEq, Repr

/-- The deponent linkage of *cōnārī* has a single stem and the voice-flipping
property mapping `pm2c` ([stump-2016] §12.1), which sends an active content cell
to a passive form cell. -/
def conariLinkage : Linkage LatinVerb LatinStem Cell Cell where
  realize := fun _ _ ↦ {.cona}
  pm := fun _ σ ↦ { σ with voice := .passive }

/-- The regular linkage of *parāre* has a single stem and the identity property
mapping, canonical on the voice axis ([stump-2016] §7.1). -/
def parareLinkage : Linkage LatinVerb LatinStem Cell Cell where
  realize := fun _ _ ↦ {.para}
  pm := fun _ σ ↦ σ

/-- `conariContentCells` lists *cōnārī*'s six active content cells ([stump-2016] Table 12.2). -/
def conariContentCells : List Cell :=
  [⟨.s1, .active⟩, ⟨.s2, .active⟩, ⟨.s3, .active⟩,
   ⟨.p1, .active⟩, ⟨.p2, .active⟩, ⟨.p3, .active⟩]

/-- The regular verb's linkage is canonical, property-set preserving (`pm = id`)
and stem invariant ([stump-2016] §7.1, characteristics (2a)–(2b)). -/
theorem parareLinkage_isCanonical : parareLinkage.IsCanonical id :=
  Linkage.canonical_isCanonical Function.injective_id fun _ : LatinVerb ↦ LatinStem.para

theorem conari_pm_flips_voice (l : LatinVerb) (σ : Cell) :
    (conariLinkage.pm l σ).voice = .passive := rfl

theorem conari_deviates_on_every_active_cell (l : LatinVerb) (σ : Cell)
    (h : σ.voice = .active) : conariLinkage.pm l σ ≠ σ := by
  intro heq
  have : Voice.passive = Voice.active := h ▸ congrArg Cell.voice heq
  exact absurd this (by decide)

theorem conariLinkage_not_canonical : ¬ conariLinkage.IsCanonical id := by
  rintro ⟨-, -, -, -, hpp⟩
  exact conari_deviates_on_every_active_cell .conari ⟨.s1, .active⟩ rfl (hpp _ _)

/-- Every content cell of *cōnārī*, active ones included, has a *passive* form
correspondent, so active content is realized by passive morphology
([stump-2016] §12.1). -/
theorem conari_active_realized_by_passive_form (l : LatinVerb) (σ : Cell) :
    (conariLinkage.corr l σ).image (·.2.voice) = {.passive} := by
  simp [conariLinkage, Linkage.corr]

theorem conari_all_cells_cross_voice :
    ∀ σ ∈ conariContentCells, conariLinkage.pm .conari σ ≠ σ := by decide

theorem depon_vs_regular (σ : Cell) (h : σ.voice = .active) :
    (parareLinkage.corr .parare σ).image (·.2.voice) = {.active} ∧
      (conariLinkage.corr .conari σ).image (·.2.voice) = {.passive} :=
  ⟨by simp [parareLinkage, Linkage.corr, h], by simp [conariLinkage, Linkage.corr]⟩

/-! ### Kashmiri morphomic tense (Ch. 8, pp. 217ff) -/

section Kashmiri

open Morphology.Exponence Morphology.PFM

/-- `KVerb` has the two intransitive verbs `WUP` 'burn inside' (Conj II) and `WUPH` 'fly'
(Conj III). -/
inductive KVerb | wup | wuph
  deriving DecidableEq, Fintype

/-- The content properties of `KContent` are the recent, indefinite and remote preterites and
1sg masculine agreement. -/
inductive KContent
  | recentPast | indefPast | remotePast
  | p1 | sg | masc
  deriving DecidableEq, Fintype

/-- The form properties of `KForm` are the morphomes 'past a' to 'past d' and 1sg masculine
agreement. -/
inductive KForm
  | pastA | pastB | pastC | pastD
  | p1 | sg | masc
  deriving DecidableEq, Fintype

open KVerb

/-- `stemOf` gives each verb its stem. -/
def stemOf : KVerb → String
  | wup => "wup"
  | wuph => "wuph"

/-- Conjugation II sends the recent past to 'past a', the indefinite past to 'past b' and the
remote past to 'past c', and each agreement property to itself. -/
def morphomeII : KContent → KForm
  | .recentPast => .pastA | .indefPast => .pastB | .remotePast => .pastC
  | .p1 => .p1 | .sg => .sg | .masc => .masc

/-- Conjugation III sends the recent past to 'past b', the indefinite past to 'past c' and the
remote past to 'past d', and each agreement property to itself. -/
def morphomeIII : KContent → KForm
  | .recentPast => .pastB | .indefPast => .pastC | .remotePast => .pastD
  | .p1 => .p1 | .sg => .sg | .masc => .masc

/-- The property mapping for Conjugation II ([stump-2016] Ch. 8) replaces each content property
by its image under `morphomeII`. -/
def pmII (σ : Finset KContent) : Finset KForm := σ.image morphomeII

/-- The property mapping for Conjugation III ([stump-2016] Ch. 8) replaces each content property
by its image under `morphomeIII`. The one-morphome shift from `pmII` is what makes the two
conjugations' preterites interleave. -/
def pmIII (σ : Finset KContent) : Finset KForm := σ.image morphomeIII

/-- The form paradigm has a 1sg masculine exponent for each morphome, read off the
stem+suffix segmentation (`wupus`, `wupyōs`, `wupyās`, `wuphiyās`). -/
def formBlock : Block KVerb String (Finset KForm) :=
  [ ⟨Finset.univ, {.pastA, .p1, .sg, .masc}, .const (· ++ "us")⟩,
    ⟨Finset.univ, {.pastB, .p1, .sg, .masc}, .const (· ++ "yōs")⟩,
    ⟨Finset.univ, {.pastC, .p1, .sg, .masc}, .const (· ++ "yās")⟩,
    ⟨Finset.univ, {.pastD, .p1, .sg, .masc}, .const (· ++ "iyās")⟩,
    (identityDefault : PFM.Rule KVerb (Finset KForm) (Action String (Finset KForm))) ]

/-- A form cell `⟨Z, τ⟩` realizes as the value of the PFM1 paradigm function on the
stem `Z` at the morphomic property set `τ`. -/
def realizeForm (z : String) (τ : Finset KForm) : String :=
  (paradigmFunction (fun _ ↦ wup) (fun _ ↦ z) [formBlock] (wup, τ)).1

/-- The Conjugation II linkage has the single stem and the property mapping `pmII`. -/
def linkII : Linkage KVerb String (Finset KContent) (Finset KForm) where
  realize l _ := {stemOf l}
  pm _ := pmII

/-- The Conjugation III linkage has the single stem and the property mapping `pmIII`. -/
def linkIII : Linkage KVerb String (Finset KContent) (Finset KForm) where
  realize l _ := {stemOf l}
  pm _ := pmIII

/-- WUP's recent past realizes as `wupus` through 'past a'. -/
example : linkII.realized realizeForm wup {.recentPast, .p1, .sg, .masc}
    = {("wupus", {.pastA, .p1, .sg, .masc})} := by decide

/-- WUP's indefinite past realizes as `wupyōs` through 'past b'. -/
example : linkII.realized realizeForm wup {.indefPast, .p1, .sg, .masc}
    = {("wupyōs", {.pastB, .p1, .sg, .masc})} := by decide

/-- WUP's remote past realizes as `wupyās` through 'past c'. -/
example : linkII.realized realizeForm wup {.remotePast, .p1, .sg, .masc}
    = {("wupyās", {.pastC, .p1, .sg, .masc})} := by decide

/-- WUPH's recent past realizes as `wuphyōs` through 'past b'. -/
example : linkIII.realized realizeForm wuph {.recentPast, .p1, .sg, .masc}
    = {("wuphyōs", {.pastB, .p1, .sg, .masc})} := by decide

/-- WUPH's indefinite past realizes as `wuphyās` through 'past c'. -/
example : linkIII.realized realizeForm wuph {.indefPast, .p1, .sg, .masc}
    = {("wuphyās", {.pastC, .p1, .sg, .masc})} := by decide

/-- WUPH's remote past realizes as `wuphiyās` through 'past d'. -/
example : linkIII.realized realizeForm wuph {.remotePast, .p1, .sg, .masc}
    = {("wuphiyās", {.pastD, .p1, .sg, .masc})} := by decide

/-- WUP's indefinite past and WUPH's recent past share their form correspondent property set, so
they inflect alike ([stump-2016] Ch. 8). -/
theorem kashmiri_inflect_alike :
    (linkII.corr wup {.indefPast, .p1, .sg, .masc}).image Prod.snd
      = (linkIII.corr wuph {.recentPast, .p1, .sg, .masc}).image Prod.snd := by decide

theorem kashmiri_inflect_alike_pastC :
    (linkII.corr wup {.remotePast, .p1, .sg, .masc}).image Prod.snd
      = (linkIII.corr wuph {.indefPast, .p1, .sg, .masc}).image Prod.snd := by decide

theorem morphomeII_injective : Function.Injective morphomeII := by decide

theorem linkII_not_syncretic : ¬ linkII.IsSyncretic :=
  fun h ↦ linkII.not_isInjective_iff.mpr h <|
    Linkage.isInjective_of_injective_pm fun _ ↦ Finset.image_injective morphomeII_injective

end Kashmiri

end Stump2016
