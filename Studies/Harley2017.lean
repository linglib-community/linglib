module

public import Linglib.Core.Order.Partition.IntervalPartition
public import Linglib.Morphology.DistributedMorphology.Basic
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Studies.Pylkkanen2008

/-!
# Harley (2017): The "bundling" hypothesis and the disparate functions of little v

Harley follows Pylkkänen in letting the functions of little v be bundled on one head or split
across several, and closes with a hierarchy of verbal projections over the root, vP > ApplP >
CausP1 > VoiceP > CausP2 (49), each language realizing some of them and bundling some of those it
realizes. A pattern is an interval partition of the projections a structure realizes, its heads
the parts. On Key's account of Turkish the root-specific allomorphs of the lexical causative are
specified for v and Caus together, so they realize only a head bundling the two, whatever its
context, while the elsewhere *-DIr* realizes Caus alone.

## Main definitions

* `Feature`: the projections of (49), from the root up.
* `turkish`, `hiaki`, `korean`, `italian`: the patterns of (49a–d).
* `vocabulary`: Key's Turkish causative vocabulary.
* `ofCauseHead`: Pylkkänen's root- and verb-selecting causative heads on the hierarchy.

## Main statements

* `voice_mem_part_v_iff`: of the four patterns only Italian bundles v with Voice.
* `v_mem_of_applies`: a lexical causative allomorph applies to the Caus head only where v is
  bundled with it, in every context.
* `subsetPrinciple_lexical`, `subsetPrinciple_productive`: the root's allomorph in the lexical
  causative, and *-DIr* in the productive one even next to the root.
* `hasCauseePosition_iff`: Pylkkänen's causee position exists exactly where v and Voice head
  separate projections.

## Implementation notes

* A projection that (49) calls distinct is a part of its own, and an absent projection lies
  outside the support.
* Pylkkänen's phase-selecting Cause sits above an embedded Voice the hierarchy has no second place
  for, so `ofCauseHead` reads only root- and verb-selecting heads.

## TODO

* The bundling diagnostics of Chol, Persian, Hiaki and Chemehuevi, the complementarity of passive
  and light verb constructions in Italian, and the footnote setting English apart from
  Pylkkänen's Voice-bundling English.

## References

* [harley-2017]
* [pylkkanen-2008]
* [key-2013]
-/

@[expose] public section

namespace Harley2017

open DistributedMorphology Morphology.Exponence

/-! ### The hierarchy (49) and its patterns -/

/-- The verbal projections of (49), from the root up. -/
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

/-- (49a) Turkish: v, the lower Caus and Voice each head a projection, with no Appl and no
upper Caus. -/
def turkish : IntervalPartition Feature := .discrete {.v, .caus₁, .voice}

/-- (49b) Hiaki: all five project, each separately. -/
def hiaki : IntervalPartition Feature := .discrete .univ

/-- (49c) Korean: v and Appl separate, no lower Caus, the upper Caus bundled with Voice. -/
def korean : IntervalPartition Feature := ⟨[{.v}, {.appl}, {.voice, .caus₂}], by decide, by decide⟩

/-- (49d) Italian: v bundled with Voice, with no Appl and no lower Caus. -/
def italian : IntervalPartition Feature := .indiscrete {.v, .voice} (by decide)

/-- Of the four patterns only Italian puts Voice on the head of v, as the chapter classifies
Italian with the bundling languages and Hiaki and Korean with the splitting ones. -/
theorem voice_mem_part_v_iff :
    ∀ P ∈ [turkish, hiaki, korean, italian], Feature.voice ∈ P.part .v ↔ P = italian := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨iff_of_false ?_ (ne_of_apply_ne IntervalPartition.support ?_),
    iff_of_false ?_ (ne_of_apply_ne IntervalPartition.support ?_),
    iff_of_false ?_ (ne_of_apply_ne IntervalPartition.support ?_), iff_of_true ?_ (by trivial)⟩
  all_goals simp [turkish, hiaki, korean, italian]
  all_goals decide

/-! ### Key's Turkish causatives -/

/-- The causative exponents: a root's lexical allomorph, or the elsewhere *-DIr*. -/
inductive Exponent where
  /-- The lexical allomorph listed for the root `ρ`. -/
  | lexical (ρ : Root)
  /-- The elsewhere *-DIr*. -/
  | dir
  deriving DecidableEq, Repr

/-- The terminal of a head, its projections as features, beside roots. -/
abbrev Terminal := Finset (Feature ⊕ Root)

/-- The lexical causative allomorph of `ρ` realizes v and Caus together next to `ρ`. -/
def lexicalItem (ρ : Root) : VocabularyItem (Feature ⊕ Root) Exponent :=
  ⟨{(0, .inl .v), (0, .inl .caus₁), (-1, .inr ρ)}, .lexical ρ⟩

/-- The elsewhere *-DIr* realizes Caus alone. -/
def dirItem : VocabularyItem (Feature ⊕ Root) Exponent := {.inl .caus₁} ⟷ .dir

/-- Key's vocabulary for a root with a listed lexical causative. -/
def vocabulary (ρ : Root) : RuleSet (VocabularyItem (Feature ⊕ Root) Exponent) :=
  [lexicalItem ρ, dirItem]

/-- The lexical allomorph is listed before *-DIr*, which it is more specific than. -/
private theorem vocabulary_pairwise (ρ : Root) :
    (vocabulary ρ).Pairwise fun i j ↦ j.specificity ≤ i.specificity := by
  have hlt : lexicalItem ρ < dirItem := by
    refine lt_of_le_not_ge (VocabularyItem.le_iff.2 ?_) fun h ↦ ?_
    · simp [Finset.subset_iff, lexicalItem, dirItem]
    · have hρ : ((-1 : ℤ), (.inr ρ : Feature ⊕ Root)) ∈ (lexicalItem ρ).site := by
        simp [lexicalItem]
      simpa [dirItem] using VocabularyItem.le_iff.1 h hρ
  simpa [vocabulary] using (VocabularyItem.specificity_strictAnti hlt).le

/-- The terminal of the head bearing the lower Caus. -/
def causTerminal (P : IntervalPartition Feature) : Terminal :=
  (P.part .caus₁).map .inl

/-- The lexical causative bundles v with the lower Caus. -/
def lexical : IntervalPartition Feature := ⟨[{.v, .caus₁}, {.voice}], by decide, by decide⟩

theorem lexical_part_caus₁ : lexical.part .caus₁ = {.v, .caus₁} := by decide

/-- **No phase boundary needed.** A lexical causative allomorph applies to the head bearing Caus
only where that head bundles v with it, in every context. -/
theorem v_mem_of_applies {P : IntervalPartition Feature} {ρ : Root} {l r : List Terminal}
    (h : Applies (lexicalItem ρ) (⟨causTerminal P, l, r⟩ : Neighborhood Terminal)) :
    Feature.v ∈ P.part .caus₁ := by
  simpa [Neighborhood.mem_def, causTerminal] using h (0, .inl .v) (by simp [lexicalItem])

/-- In the lexical causative next to its root, the root's allomorph wins. -/
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

/-- In the productive causative of (49a) *-DIr* wins, even next to the root. -/
theorem subsetPrinciple_productive (ρ : Root) (l r : List Terminal) :
    subsetPrinciple (vocabulary ρ) ⟨causTerminal turkish, l, r⟩ = some .dir := by
  have hl : ¬ Applies (lexicalItem ρ) (⟨causTerminal turkish, l, r⟩ : Neighborhood _) :=
    fun h ↦ by simpa [turkish] using v_mem_of_applies h
  have hd : Applies dirItem (⟨causTerminal turkish, l, r⟩ : Neighborhood _) := by
    simp [dirItem, causTerminal, turkish]
  rw [subsetPrinciple_eq_head?_applicable (vocabulary_pairwise ρ),
    show RuleSet.applicable (vocabulary ρ) _ = [dirItem] by
      simp [RuleSet.applicable, vocabulary, hl, hd]]
  rfl

/-! ### Pylkkänen's causative heads -/

open Pylkkanen2008 in
/-- Pylkkänen's root- and verb-selecting causative heads on the hierarchy, as the chapter reads
them after [key-2013]: a root-selecting Cause, a lexical causative, bundles v with Caus, and a
verb-selecting Cause is the lower Caus over a separate v; Voice-bundling puts Caus on Voice's
head. -/
def ofCauseHead : CauseHead → Option (IntervalPartition Feature)
  | ⟨.root, true⟩ => some (.indiscrete {.v, .caus₁, .voice} (by decide))
  | ⟨.root, false⟩ => some lexical
  | ⟨.verb, true⟩ => some ⟨[{.v}, {.caus₁, .voice}], by decide, by decide⟩
  | ⟨.verb, false⟩ => some turkish
  | ⟨.phase, _⟩ => none

/-- **Pylkkänen's causee generalization as bundling.** On the chapter's reading a causee position
exists exactly where v and Voice head separate projections. -/
theorem hasCauseePosition_iff {c : Pylkkanen2008.CauseHead} {P : IntervalPartition Feature}
    (h : ofCauseHead c = some P) : c.HasCauseePosition ↔ Feature.voice ∉ P.part .v := by
  obtain ⟨_ | _ | _, _ | _⟩ := c <;> cases h <;>
    simp [Pylkkanen2008.hasCauseePosition_iff, lexical, turkish] <;> decide

end Harley2017
