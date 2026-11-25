module

public import Linglib.Core.Order.OrdConnected
public import Linglib.Data.Examples.Harley2017
public import Linglib.Morphology.DistributedMorphology.Basic
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Mathlib.Order.Partition.Finpartition
public import Studies.Pylkkanen2008

/-!
# Harley (2017): The "bundling" hypothesis and the disparate functions of little v

Harley adopts Pylkkänen's view that the features of the verbal domain may be bundled on one head
or split across several, and proposes the hierarchy of projections
vP > ApplP > CausP1 > VoiceP > CausP2. A causative feature is expressed at three positions of it:
the two causative projections project [+CAUS], and the verbalizer of a lexical causative bears it
besides [+v]. A pattern is a partition of the projections a structure realizes; its parts are the
heads, and the terminal of a head bears the features of its projections.

Read as spanning, in the sense of [svenonius-2012], the hierarchy constrains the patterns: a head
bundles only projections that are neighbours among those realized. The patterns Harley gives for
Turkish, Hiaki, Korean and Italian are of this kind. In such a pattern a head bearing v and Voice
bears every projection realized up to Voice, so an applicative or a lower Caus has no head of its
own.

Key's analysis of Turkish causatives follows by Vocabulary Insertion over the terminals. The
lexical causative allomorph of a root is specified for [+v, +CAUS] and the elsewhere *-DIr* for
[+CAUS]. The allomorph is therefore inserted exactly at a terminal bearing both features next to
its root. A head with a causative projection and without v is realized by *-DIr* in every
context, whichever causative projection it is and whatever else the head bundles, and a
structure expressing the causative feature at all three positions has *-DIr* at each of them
when its root has no allomorph.

Pylkkänen's causative heads are read on the hierarchy: Cause is expressed on v when it selects a
root, at the lower Caus when it selects a verb and at the upper Caus when it selects a phase, and
is bundled with Voice when its position is on the head of Voice. The patterns of the six heads
bundle only neighbours, a head has a causee position iff its pattern puts v and Voice on
different heads, and only a root-selecting Cause is realized by an allomorph of the root.

The order of the hierarchy is paired with Jung's Hiaki judgments: an applicative suffix outside a
causative one is acceptable when the causative is lexical, expressed on v below the applicative,
and unacceptable when it is the causative of an unergative, expressed at the upper Caus.

## Implementation notes

* A projection absent from a pattern lies outside the set it partitions; the projections Harley
  calls distinct are singleton parts.
* Harley raises spanning only as an alternative to bundling, so that the heads bundle only
  neighbours is a hypothesis, or a theorem about a pattern, and not part of the type of patterns.
* The causative flavor of the verbalizer is an argument of `terminal`, the features v bears
  besides [+v], and not a projection: in [key-2013] a lexical causative occurs below the
  productive causative head.
* The hierarchy has one Voice. The Korean pattern and the pattern of a phase-selecting Cause
  bundled with Voice put the upper Caus on the head of that Voice, which is below it; the Voice
  above a phase-selecting Cause is not represented.
* `vocabulary ρ` lists the allomorph of the one root `ρ`; any other root has none.

## TODO

* Harley's diagnostics for Chol, Persian, Hiaki and Chemehuevi; Italian passives and light verb
  constructions; the footnote setting English apart from Pylkkänen's analysis.

## References

* [harley-2017]
* [pylkkanen-2008]
* [key-2013]
* [svenonius-2012]
-/

@[expose] public section

namespace Harley2017

open DistributedMorphology Morphology

/-! ### The hierarchy and its patterns -/

/-- The verbal projections of (49), in order from the root. -/
inductive Projection where
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

instance : LinearOrder Projection := LinearOrder.lift' Projection.ctorIdx (by decide)

/-- The features the projections of (49) project. -/
inductive Feature where
  /-- The verbalizing [+v]. -/
  | v
  /-- The applicative feature. -/
  | appl
  /-- The causative [+CAUS]. -/
  | caus
  /-- The feature of Voice. -/
  | voice
  deriving DecidableEq, Repr

/-- The features a projection contributes to its head, where the verbalizer bears `fv` besides
[+v]; the two causative projections project the one [+CAUS]. -/
def Projection.features (fv : Finset Feature) : Projection → Finset Feature
  | .v => insert .v fv
  | .appl => {.appl}
  | .caus₁ | .caus₂ => {.caus}
  | .voice => {.voice}

/-- v, the lower Caus and Voice, the projections of (49a) and of Pylkkänen's causatives. -/
abbrev vCausVoice : Finset Projection := {.v, .caus₁, .voice}

/-- (49a) Turkish: v, the lower Caus and Voice on separate heads. -/
def turkish : Finpartition vCausVoice := ⊥

/-- (49b) Hiaki: all five projections on separate heads. -/
def hiaki : Finpartition (.univ : Finset Projection) := ⊥

/-- (49c) Korean: v and Appl on separate heads, the upper Caus on the head of Voice. -/
def korean : Finpartition ({.v, .appl, .voice, .caus₂} : Finset Projection) :=
  ⟨{{.v}, {.appl}, {.voice, .caus₂}}, by decide, by decide, by decide⟩

/-- (49d) Italian: v and Voice on one head. -/
def italian : Finpartition ({.v, .voice} : Finset Projection) := .indiscrete (by decide)

-- among (49a–d), only Italian puts Voice on the head of v
theorem voice_mem_part_v :
    Projection.voice ∉ turkish.part .v ∧ Projection.voice ∉ hiaki.part .v ∧
      Projection.voice ∉ korean.part .v ∧ Projection.voice ∈ italian.part .v := by
  decide

-- (49), read as spanning: each head bundles only projections neighbouring among those realized
theorem patterns_isContiguous :
    IsContiguous (fun x : vCausVoice ↦ turkish.part x) ∧
      IsContiguous (fun x : (.univ : Finset Projection) ↦ hiaki.part x) ∧
      IsContiguous (fun x : ({.v, .appl, .voice, .caus₂} : Finset Projection) ↦ korean.part x) ∧
      IsContiguous (fun x : ({.v, .voice} : Finset Projection) ↦ italian.part x) := by
  decide

-- a head bundling v with Voice past a realized lower Caus is not a span
example : ¬ IsContiguous fun x : vCausVoice ↦
    (⟨{{.v, .voice}, {.caus₁}}, by decide, by decide, by decide⟩ :
      Finpartition vCausVoice).part x := by
  decide

section Pattern

variable {s : Finset Projection} {P : Finpartition s} {x : Projection}

/-- In a pattern whose heads bundle only neighbours, a head bearing v and Voice bears every
projection realized up to Voice, so an applicative or a lower Caus has no head of its own. -/
theorem part_eq_part_v_of_voice_mem (hP : IsContiguous fun x : s ↦ P.part x)
    (h : Projection.voice ∈ P.part .v) (hx : x ∈ s) (hle : x ≤ .voice) :
    P.part x = P.part .v :=
  have hv : Projection.v ∈ s := P.part_nonempty.1 ⟨_, h⟩
  have hvoice : Projection.voice ∈ s := P.part_subset _ h
  (hP (i := ⟨.v, hv⟩) (j := ⟨x, hx⟩) (k := ⟨.voice, hvoice⟩)
    (show Projection.v ≤ x by cases x <;> decide) hle
    ((P.mem_part_iff_part_eq_part hvoice hv).1 h).symm).symm

-- (24b-ii): a pattern with a high applicative on a head of its own splits Voice from v
theorem voice_notMem_part_v_of_part_appl_ne (hP : IsContiguous fun x : s ↦ P.part x)
    (hs : Projection.appl ∈ s) (h : P.part .appl ≠ P.part .v) : Projection.voice ∉ P.part .v :=
  fun hv ↦ h (part_eq_part_v_of_voice_mem hP hv hs (by decide))

/-! ### Key's Turkish causatives -/

/-- The Turkish causative exponents. -/
inductive Exponent where
  /-- The lexical allomorph of the root `ρ`. -/
  | lexical (ρ : Root)
  /-- The elsewhere *-DIr*. -/
  | dir
  deriving DecidableEq, Repr

/-- Terminals: finsets of features and roots. -/
abbrev Terminal := Finset (Feature ⊕ Root)

variable {fv : Finset Feature}

/-- The terminal of the head of `x`, bearing the features of its projections, where the
verbalizer bears `fv` besides [+v]. -/
def terminal (P : Finpartition s) (fv : Finset Feature) (x : Projection) : Terminal :=
  ((P.part x).biUnion (·.features fv)).map .inl

@[simp] theorem inl_mem_terminal {f : Feature} :
    Sum.inl f ∈ terminal P fv x ↔ ∃ y ∈ P.part x, f ∈ y.features fv := by
  simp [terminal]

theorem inl_v_mem_terminal : Sum.inl Feature.v ∈ terminal P fv x ↔ Projection.v ∈ P.part x := by
  rw [inl_mem_terminal]
  refine ⟨fun ⟨y, hy, h⟩ ↦ ?_, fun h ↦ ⟨_, h, Finset.mem_insert_self _ _⟩⟩
  cases y <;> first | exact hy | simp [Projection.features] at h

/-- The lexical causative allomorph of `ρ`, realizing [+v, +CAUS] next to `ρ`. -/
def lexicalItem (ρ : Root) : VocabularyItem (Feature ⊕ Root) Exponent :=
  ⟨{(0, .inl .v), (0, .inl .caus), (-1, .inr ρ)}, .lexical ρ⟩

/-- (36): the elsewhere *-DIr*, realizing [+CAUS]. -/
def dirItem : VocabularyItem (Feature ⊕ Root) Exponent := {.inl .caus} ⟷ .dir

/-- Key's vocabulary for a root `ρ` with a lexical causative allomorph. -/
def vocabulary (ρ : Root) : RuleSet (VocabularyItem (Feature ⊕ Root) Exponent) :=
  [lexicalItem ρ, dirItem]

variable {ρ ρ' : Root} {n : Neighborhood Terminal}

theorem applies_lexicalItem_iff : Applies (lexicalItem ρ) n ↔
    Sum.inl Feature.v ∈ n.focus ∧ Sum.inl Feature.caus ∈ n.focus ∧ Sum.inr ρ ∈ n.nth (-1) := by
  simp [VocabularyItem.applies_iff, lexicalItem, Neighborhood.mem_def]

theorem applies_dirItem_iff : Applies dirItem n ↔ Sum.inl Feature.caus ∈ n.focus := by
  simp [dirItem]

private theorem vocabulary_pairwise (ρ : Root) :
    (vocabulary ρ).Pairwise fun i j ↦ j.specificity ≤ i.specificity := by
  have hlt : applySet (lexicalItem ρ) ⊂ applySet dirItem := by
    refine ssubset_of_subset_not_subset (VocabularyItem.applySet_subset_iff.2 ?_) fun h ↦ ?_
    · simp [Finset.subset_iff, lexicalItem, dirItem]
    · have hρ : ((-1 : ℤ), (.inr ρ : Feature ⊕ Root)) ∈ (lexicalItem ρ).site := by
        simp [lexicalItem]
      simpa [dirItem] using VocabularyItem.applySet_subset_iff.1 h hρ
  simpa [vocabulary] using (VocabularyItem.specificity_lt_of_applySet_ssubset hlt).le

-- the allomorph of `ρ` where it applies, *-DIr* at any other terminal bearing [+CAUS]
theorem subsetPrinciple_vocabulary (ρ : Root) (n : Neighborhood Terminal) :
    subsetPrinciple (vocabulary ρ) n =
      if Applies (lexicalItem ρ) n then some (.lexical ρ)
      else if Sum.inl Feature.caus ∈ n.focus then some .dir else none := by
  rw [subsetPrinciple_eq_head?_applicable (vocabulary_pairwise ρ)]
  by_cases hl : Applies (lexicalItem ρ) n <;> by_cases hd : Applies dirItem n <;>
    simp [RuleSet.applicable, vocabulary, hl, hd, ← applies_dirItem_iff] <;> rfl

-- the allomorph of a root is inserted exactly at a terminal bearing [+v, +CAUS] next to the root
theorem subsetPrinciple_eq_lexical_iff : subsetPrinciple (vocabulary ρ) n = some (.lexical ρ) ↔
    Sum.inl Feature.v ∈ n.focus ∧ Sum.inl Feature.caus ∈ n.focus ∧ Sum.inr ρ ∈ n.nth (-1) := by
  rw [subsetPrinciple_vocabulary, ← applies_lexicalItem_iff]
  split_ifs <;> simp [*]

-- *-DIr* is inserted at the other terminals bearing [+CAUS]
theorem subsetPrinciple_eq_dir_iff : subsetPrinciple (vocabulary ρ) n = some .dir ↔
    Sum.inl Feature.caus ∈ n.focus ∧
      ¬ (Sum.inl Feature.v ∈ n.focus ∧ Sum.inr ρ ∈ n.nth (-1)) := by
  have h := applies_lexicalItem_iff (ρ := ρ) (n := n)
  rw [subsetPrinciple_vocabulary]
  split_ifs <;> simp_all

/-- A head with a causative projection and without v is realized by *-DIr* in every context,
whichever causative projection it is and whatever else the head bundles. -/
theorem subsetPrinciple_terminal_of_v_notMem (ρ : Root) (hx : x ∈ s)
    (hc : Feature.caus ∈ x.features fv) (hv : Projection.v ∉ P.part x) (l r : List Terminal) :
    subsetPrinciple (vocabulary ρ) ⟨terminal P fv x, l, r⟩ = some .dir :=
  subsetPrinciple_eq_dir_iff.2
    ⟨inl_mem_terminal.2 ⟨x, P.mem_part_self.2 hx, hc⟩, fun h ↦ hv (inl_v_mem_terminal.1 h.1)⟩

-- the productive causative (49a)
theorem subsetPrinciple_turkish (ρ : Root) (l r : List Terminal) :
    subsetPrinciple (vocabulary ρ) ⟨terminal turkish fv .caus₁, l, r⟩ = some .dir :=
  subsetPrinciple_terminal_of_v_notMem ρ (by decide) (Finset.mem_singleton_self _) (by decide) l r

-- the verbalizer of a lexical causative: the allomorph of the root next to it, or else *-DIr*
theorem subsetPrinciple_terminal_v (ρ ρ' : Root) (hv : Projection.v ∈ s) (r : List Terminal) :
    subsetPrinciple (vocabulary ρ) ⟨terminal P {.caus} .v, [{.inr ρ'}], r⟩ =
      some (if ρ' = ρ then .lexical ρ else .dir) := by
  have hcaus : Sum.inl Feature.caus ∈ terminal P {.caus} .v :=
    inl_mem_terminal.2 ⟨.v, P.mem_part_self.2 hv, by simp [Projection.features]⟩
  have hvt : Sum.inl Feature.v ∈ terminal P {.caus} .v :=
    inl_v_mem_terminal.2 (P.mem_part_self.2 hv)
  split_ifs with h
  · exact subsetPrinciple_eq_lexical_iff.2 ⟨hvt, hcaus, by simp [h]⟩
  · exact subsetPrinciple_eq_dir_iff.2 ⟨hcaus, fun h' ↦ h (by simpa [eq_comm] using h'.2)⟩

/-- A structure that expresses the causative feature on v and at both causative projections,
each on a head of its own, has *-DIr* at all three when its root has no allomorph. -/
theorem subsetPrinciple_eq_dir_of_ne (h : ρ' ≠ ρ) (hv : Projection.v ∈ s)
    (h₁ : Projection.caus₁ ∈ s) (h₂ : Projection.caus₂ ∈ s)
    (hv₁ : Projection.v ∉ P.part .caus₁) (hv₂ : Projection.v ∉ P.part .caus₂)
    (r l₁ r₁ l₂ r₂ : List Terminal) :
    subsetPrinciple (vocabulary ρ) ⟨terminal P {.caus} .v, [{.inr ρ'}], r⟩ = some .dir ∧
      subsetPrinciple (vocabulary ρ) ⟨terminal P {.caus} .caus₁, l₁, r₁⟩ = some .dir ∧
      subsetPrinciple (vocabulary ρ) ⟨terminal P {.caus} .caus₂, l₂, r₂⟩ = some .dir :=
  ⟨by simp [subsetPrinciple_terminal_v ρ ρ' hv, h],
    subsetPrinciple_terminal_of_v_notMem ρ h₁ (Finset.mem_singleton_self _) hv₁ l₁ r₁,
    subsetPrinciple_terminal_of_v_notMem ρ h₂ (Finset.mem_singleton_self _) hv₂ l₂ r₂⟩

-- (49b) is such a pattern
example (h : ρ' ≠ ρ) (r l₁ r₁ l₂ r₂ : List Terminal) :=
  subsetPrinciple_eq_dir_of_ne (P := hiaki) h (by decide) (by decide) (by decide) (by decide)
    (by decide) r l₁ r₁ l₂ r₂

end Pattern

/-! ### Pylkkänen's causative heads -/

section CauseHead

open Pylkkanen2008

/-- The position at which a causative head expresses [+CAUS]: on v when it selects a root, at the
lower Caus when it selects a verb, and at the upper Caus when it selects a phase. -/
def causPosition : Layer → Projection
  | .root => .v
  | .verb => .caus₁
  | .phase => .caus₂

/-- The position of Cause rises with the layer it selects. -/
def causPositionEmbedding : Layer ↪o Projection where
  toFun := causPosition
  inj' := by decide
  map_rel_iff' {l m} := by cases l <;> cases m <;> decide +kernel

@[simp] theorem coe_causPositionEmbedding : ⇑causPositionEmbedding = causPosition := rfl

/-- The features the verbalizer bears besides [+v] below a causative head: [+CAUS] when Cause
selects a root. -/
def vFeatures : Layer → Finset Feature
  | .root => {.caus}
  | _ => ∅

/-- The projections a causative structure realizes: v, Voice and the position of Cause. -/
abbrev realized (l : Layer) : Finset Projection := {.v, .voice, causPosition l}

/-- The pattern of a causative head: the position of Cause is on the head of Voice when the two
are bundled, and every other projection is on a head of its own. -/
def pattern : (c : CauseHead) → Finpartition (realized c.selects)
  | ⟨.root, true⟩ => .indiscrete (by decide)
  | ⟨.verb, true⟩ => ⟨{{.v}, {.caus₁, .voice}}, by decide, by decide, by decide⟩
  | ⟨.phase, true⟩ => ⟨{{.v}, {.voice, .caus₂}}, by decide, by decide, by decide⟩
  | ⟨_, false⟩ => ⊥

variable (c : CauseHead)

-- Cause is bundled with Voice iff its position is on the head of Voice
theorem voice_mem_part_causPosition_iff :
    Projection.voice ∈ (pattern c).part (causPosition c.selects) ↔ c.bundled = true := by
  obtain ⟨_ | _ | _, _ | _⟩ := c <;> decide

-- the heads of Pylkkänen's patterns bundle only neighbours
theorem isContiguous_pattern : IsContiguous fun x : realized c.selects ↦ (pattern c).part x := by
  obtain ⟨_ | _ | _, _ | _⟩ := c <;> decide

-- the verb-selecting Cause that is not bundled with Voice has the pattern (49a)
theorem parts_pattern_verb : (pattern ⟨.verb, false⟩).parts = turkish.parts := by decide

/-- A causative head has a causee position iff its pattern puts v and Voice on different heads. -/
theorem hasCauseePosition_iff : c.HasCauseePosition ↔ Projection.voice ∉ (pattern c).part .v := by
  obtain ⟨_ | _ | _, _ | _⟩ := c <;>
    simp [Pylkkanen2008.hasCauseePosition_iff] <;> decide

-- under Key's vocabulary only a root-selecting Cause is realized by an allomorph of the root
theorem subsetPrinciple_causPosition (ρ : Root) (r : List Terminal) :
    subsetPrinciple (vocabulary ρ)
        ⟨terminal (pattern c) (vFeatures c.selects) (causPosition c.selects), [{.inr ρ}], r⟩ =
      some (if c.selects = .root then .lexical ρ else .dir) := by
  obtain ⟨_ | _ | _, _ | _⟩ := c
  case root.false | root.true =>
    simpa [causPosition, vFeatures] using subsetPrinciple_terminal_v ρ ρ (by decide) r
  all_goals
    exact subsetPrinciple_terminal_of_v_notMem ρ (by decide) (Finset.mem_singleton_self _)
      (by decide) _ r

end CauseHead

/-! ### Jung's Hiaki applicatives -/

open Pylkkanen2008 in
/-- The layer the causative of a verb selects: the causative of an unaccusative is lexical, and
that of an unergative, whose external argument Voice introduces, selects a phase. -/
def selects : Examples.Base → Layer
  | .unaccusative => .root
  | .unergative => .phase

/-- (47), (48): an applicative outside a causative is acceptable iff Cause is expressed below the
applicative in the hierarchy. -/
theorem applicative_iff : ∀ d ∈ Examples.all, ∀ b ∈ Examples.base d,
    d.judgment = .acceptable ↔ causPosition (selects b) < .appl := by
  decide +kernel

end Harley2017
