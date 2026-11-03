module

public import Linglib.Core.Order.OrdConnected
public import Linglib.Morphology.DistributedMorphology.Basic
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Mathlib.Order.Partition.Finpartition
public import Studies.Pylkkanen2008

/-!
# Harley (2017): The "bundling" hypothesis and the disparate functions of little v

Harley adopts Pylkkänen's view that the functions of little v may be bundled on one head or split
across several, and proposes the hierarchy vP > ApplP > CausP1 > VoiceP > CausP2 (49). A pattern
is a partition of the projections a structure realizes, whose parts are its heads, and the patterns
of (49) [bundle only neighbouring projections](##patterns_isContiguous). Key's analysis of Turkish
causatives follows by Vocabulary Insertion over these heads.

## Main definitions

* `Feature`: the projections of (49).
* `turkish`, `hiaki`, `korean`, `italian`: the patterns of (49a–d).
* `vocabulary`: Key's Turkish causative vocabulary.
* `ofCauseHead`: Pylkkänen's root- and verb-selecting causative heads as patterns.

## Implementation notes

* A projection absent from a pattern lies outside the set it partitions; the projections (49)
  calls distinct are singleton parts.
* Harley raises spanning only as an alternative to bundling, so being an interval of the realized
  projections is a theorem about the patterns of (49) rather than part of their type.
* `ofCauseHead` is undefined on phase-selecting Cause, which would need a second Voice below
  CausP2.

## TODO

* Harley's diagnostics for Chol, Persian, Hiaki and Chemehuevi; Italian passives and light verb
  constructions; the footnote setting English apart from Pylkkänen's analysis.

## References

* [harley-2017]
* [pylkkanen-2008]
* [key-2013]
-/

@[expose] public section

namespace Harley2017

open DistributedMorphology Morphology.Exponence

/-! ### The hierarchy (49) and its patterns -/

/-- The verbal projections of (49), in order from the root. -/
inductive Feature where
  /-- The verbalizer. -/
  | v
  /-- The applicative. -/
  | appl
  /-- The causative below Voice. -/
  | caus₁
  /-- Voice, which introduces the external argument. -/
  | voice
  /-- The causative above Voice. -/
  | caus₂
  deriving DecidableEq, Repr, Fintype

instance : LinearOrder Feature := LinearOrder.lift' Feature.ctorIdx (by decide)

/-- v, the lower Caus and Voice, the projections of (49a) and of Pylkkänen's causatives. -/
abbrev vCausVoice : Finset Feature := {.v, .caus₁, .voice}

/-- (49a) Turkish: v, the lower Caus and Voice on separate heads. -/
def turkish : Finpartition vCausVoice := ⊥

/-- (49b) Hiaki: all five projections on separate heads. -/
def hiaki : Finpartition (.univ : Finset Feature) := ⊥

/-- (49c) Korean: v and Appl on separate heads, the upper Caus on the head of Voice. -/
def korean : Finpartition ({.v, .appl, .voice, .caus₂} : Finset Feature) :=
  ⟨{{.v}, {.appl}, {.voice, .caus₂}}, by decide, by decide, by decide⟩

/-- (49d) Italian: v and Voice on one head. -/
def italian : Finpartition ({.v, .voice} : Finset Feature) := .indiscrete (by decide)

/-- Among (49a–d), only Italian puts Voice on the head of v. -/
theorem voice_mem_part_v :
    Feature.voice ∉ turkish.part .v ∧ Feature.voice ∉ hiaki.part .v ∧
      Feature.voice ∉ korean.part .v ∧ Feature.voice ∈ italian.part .v := by
  decide

-- (49), read as spanning: each head bundles only projections neighbouring among those realized
theorem patterns_isContiguous :
    IsContiguous (fun x : vCausVoice ↦ turkish.part x) ∧
      IsContiguous (fun x : (.univ : Finset Feature) ↦ hiaki.part x) ∧
      IsContiguous (fun x : ({.v, .appl, .voice, .caus₂} : Finset Feature) ↦ korean.part x) ∧
      IsContiguous (fun x : ({.v, .voice} : Finset Feature) ↦ italian.part x) := by
  decide

-- a head bundling v with Voice past a realized lower Caus is not a span
example : ¬ IsContiguous fun x : vCausVoice ↦
    (⟨{{.v, .voice}, {.caus₁}}, by decide, by decide, by decide⟩ :
      Finpartition vCausVoice).part x := by
  decide

/-! ### Key's Turkish causatives -/

/-- The Turkish causative exponents. -/
inductive Exponent where
  /-- The lexical allomorph of the root `ρ`. -/
  | lexical (ρ : Root)
  /-- The elsewhere *-DIr*. -/
  | dir
  deriving DecidableEq, Repr

/-- Terminals: finsets of projections and roots. -/
abbrev Terminal := Finset (Feature ⊕ Root)

/-- The lexical causative allomorph of `ρ`, realizing v and Caus in the context of `ρ`. -/
def lexicalItem (ρ : Root) : VocabularyItem (Feature ⊕ Root) Exponent :=
  ⟨{(0, .inl .v), (0, .inl .caus₁), (-1, .inr ρ)}, .lexical ρ⟩

/-- The elsewhere *-DIr*, realizing Caus. -/
def dirItem : VocabularyItem (Feature ⊕ Root) Exponent := {.inl .caus₁} ⟷ .dir

/-- Key's vocabulary for a root `ρ` with a lexical causative allomorph. -/
def vocabulary (ρ : Root) : RuleSet (VocabularyItem (Feature ⊕ Root) Exponent) :=
  [lexicalItem ρ, dirItem]

private theorem vocabulary_pairwise (ρ : Root) :
    (vocabulary ρ).Pairwise fun i j ↦ j.specificity ≤ i.specificity := by
  have hlt : applySet (lexicalItem ρ) ⊂ applySet dirItem := by
    refine ssubset_of_subset_not_subset (VocabularyItem.applySet_subset_iff.2 ?_) fun h ↦ ?_
    · simp [Finset.subset_iff, lexicalItem, dirItem]
    · have hρ : ((-1 : ℤ), (.inr ρ : Feature ⊕ Root)) ∈ (lexicalItem ρ).site := by
        simp [lexicalItem]
      simpa [dirItem] using VocabularyItem.applySet_subset_iff.1 h hρ
  simpa [vocabulary] using (VocabularyItem.specificity_lt_of_applySet_ssubset hlt).le

/-- The terminal of the head bearing the lower Caus. -/
def causTerminal {s : Finset Feature} (P : Finpartition s) : Terminal :=
  (P.part .caus₁).map .inl

/-- The lexical causative: v and the lower Caus on one head. -/
def lexical : Finpartition vCausVoice :=
  ⟨{{.v, .caus₁}, {.voice}}, by decide, by decide, by decide⟩

theorem lexical_part_caus₁ : lexical.part .caus₁ = {.v, .caus₁} := by decide

theorem turkish_part_caus₁ : turkish.part .caus₁ = {.caus₁} := by decide

/-- A lexical causative allomorph applies to the head bearing Caus only if v is on that head, in
every context. -/
theorem v_mem_of_applies {s : Finset Feature} {P : Finpartition s} {ρ : Root} {l r : List Terminal}
    (h : Applies (lexicalItem ρ) (⟨causTerminal P, l, r⟩ : Neighborhood Terminal)) :
    Feature.v ∈ P.part .caus₁ := by
  simpa [Neighborhood.mem_def, causTerminal] using h (0, .inl .v) (by simp [lexicalItem])

/-- In the lexical causative next to its root, the root's allomorph is inserted. -/
theorem subsetPrinciple_lexical (ρ : Root) :
    subsetPrinciple (vocabulary ρ) ⟨causTerminal lexical, [{.inr ρ}], []⟩ = some (.lexical ρ) := by
  have hl : Applies (lexicalItem ρ) (⟨causTerminal lexical, [{.inr ρ}], []⟩ : Neighborhood _) := by
    simp [VocabularyItem.applies_iff, lexicalItem, Neighborhood.mem_def, causTerminal,
      lexical_part_caus₁]
  have hd : Applies dirItem (⟨causTerminal lexical, [{.inr ρ}], []⟩ : Neighborhood _) := by
    simp [dirItem, causTerminal, lexical_part_caus₁]
  rw [subsetPrinciple_eq_head?_applicable (vocabulary_pairwise ρ),
    show RuleSet.applicable (vocabulary ρ) _ = [lexicalItem ρ, dirItem] by
      simp [RuleSet.applicable, vocabulary, hl, hd]]
  rfl

/-- In the productive causative (49a), *-DIr* is inserted in every context. -/
theorem subsetPrinciple_productive (ρ : Root) (l r : List Terminal) :
    subsetPrinciple (vocabulary ρ) ⟨causTerminal turkish, l, r⟩ = some .dir := by
  have hl : ¬ Applies (lexicalItem ρ) (⟨causTerminal turkish, l, r⟩ : Neighborhood _) :=
    fun h ↦ by simpa [turkish_part_caus₁] using v_mem_of_applies h
  have hd : Applies dirItem (⟨causTerminal turkish, l, r⟩ : Neighborhood _) := by
    simp [dirItem, causTerminal, turkish_part_caus₁]
  rw [subsetPrinciple_eq_head?_applicable (vocabulary_pairwise ρ),
    show RuleSet.applicable (vocabulary ρ) _ = [dirItem] by
      simp [RuleSet.applicable, vocabulary, hl, hd]]
  rfl

/-! ### Pylkkänen's causative heads -/

open Pylkkanen2008 in
/-- Pylkkänen's root- and verb-selecting causative heads as patterns, on the chapter's reading of
[key-2013]: root-selecting Cause shares the head of v, verb-selecting Cause is the lower Caus on a
head of its own, and Voice-bundling puts Cause on the head of Voice. -/
def ofCauseHead : CauseHead → Option (Finpartition vCausVoice)
  | ⟨.root, true⟩ => some (.indiscrete (by decide))
  | ⟨.root, false⟩ => some lexical
  | ⟨.verb, true⟩ => some ⟨{{.v}, {.caus₁, .voice}}, by decide, by decide, by decide⟩
  | ⟨.verb, false⟩ => some turkish
  | ⟨.phase, _⟩ => none

/-- A causative head has a causee position iff its pattern puts v and Voice on different heads. -/
theorem hasCauseePosition_iff {c : Pylkkanen2008.CauseHead} {P : Finpartition vCausVoice}
    (h : ofCauseHead c = some P) : c.HasCauseePosition ↔ Feature.voice ∉ P.part .v := by
  obtain ⟨_ | _ | _, _ | _⟩ := c <;> cases h <;>
    simp [Pylkkanen2008.hasCauseePosition_iff, lexical, turkish] <;> decide

end Harley2017
