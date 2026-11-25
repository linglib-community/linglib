module

public import Linglib.Data.Examples.Gloss
public import Linglib.Data.Examples.Harley2017
public import Linglib.Morphology.DistributedMorphology.Basic
public import Linglib.Syntax.Spine.Basic
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Studies.Pylkkanen2008

/-!
# Harley (2017): The "bundling" hypothesis and the disparate functions of little v

Harley adopts Pylkkänen's view that the features of the verbal domain may be bundled on one head
or split across several, and proposes the hierarchy of projections
vP > ApplP > CausP1 > VoiceP > CausP2. A causative feature is expressed at three positions of it:
the two causative projections project [+CAUS], and the verbalizer of a lexical causative bears it
besides [+v]. A pattern lists the heads of a structure from the root up, each with the
projections it bears. The terminal of a head bears the features of its projections, and a word is
the string of its root and its terminals.

The projections of a pattern rise along the hierarchy, so each head bears a stretch of the
projections realized, a span in the sense of [svenonius-2012]. The patterns Harley gives for
Turkish, Hiaki, Korean and Italian are of this kind. A head bearing v and Voice then bears every
projection realized up to Voice, so an applicative or a lower Caus has no head of its own.

Key's analysis of Turkish causatives follows by Vocabulary Insertion along the word, each head in
the neighbourhood of the root and the other heads. The lexical causative allomorph of a root is
specified for [+v, +CAUS] next to the root and the elsewhere *-DIr* for [+CAUS]. The lowest head
is therefore realized by the allomorph when it bears both features and the root has one, and
every other head bearing [+CAUS] is realized by *-DIr*, whichever causative projection it bears
and whatever else it bundles. A structure expressing the causative feature at all three positions
has *-DIr* at each of them when its root has no allomorph.

Pylkkänen's causative heads are read on the hierarchy: Cause is expressed on v when it selects a
root, at the lower Caus when it selects a verb and at the upper Caus when it selects a phase. The
pattern of a head joins the position of Cause to Voice when the two are bundled and gives every
other projection a head of its own. A head has a causee position iff its pattern puts v and Voice
on different heads, and only a root-selecting Cause is realized by an allomorph of the root.

The order of the hierarchy is paired with Jung's Hiaki judgments: an applicative suffix outside a
causative one is acceptable when the causative is lexical, expressed on v below the applicative,
and unacceptable when it is the causative of an unergative, expressed at the upper Caus.

## Implementation notes

* A pattern is a list of heads and not a partition of a set of projections, since the heads of a
  word come in order and insertion at a head reads its neighbours. A projection a structure does
  not realize is on no head.
* Bundling and spanning both put neighbouring projections on one head. Whether that head is one
  terminal of the syntax or several spelled out together is not represented.
* The causative flavor of the verbalizer is an argument of `terminal`, the features v bears
  besides [+v], and not a projection: in [key-2013] a lexical causative occurs below the
  productive causative head.
* The hierarchy has one Voice. The Korean pattern and the pattern of a phase-selecting Cause
  bundled with Voice put the upper Caus on the head of that Voice, which is below it; the Voice
  above a phase-selecting Cause is not represented.
* `vocabulary ρ` lists the allomorph of the one root `ρ`; any other root has none.
* The class of a Hiaki verb is read off its gloss by `base?`, which stands in for lexical
  entries: there is no Hiaki fragment to take it from.

## TODO

* Hiaki verb entries, so that the class of a causativized verb is derived and not listed.
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

/-- (49a) Turkish: v, the lower Caus and Voice on separate heads. -/
def turkish : List (List Projection) := [[.v], [.caus₁], [.voice]]

/-- (49b) Hiaki: all five projections on separate heads. -/
def hiaki : List (List Projection) := [[.v], [.appl], [.caus₁], [.voice], [.caus₂]]

/-- (49c) Korean: v and Appl on separate heads, the upper Caus on the head of Voice. -/
def korean : List (List Projection) := [[.v], [.appl], [.voice, .caus₂]]

/-- (49d) Italian: v and Voice on one head. -/
def italian : List (List Projection) := [[.v, .voice]]

-- the projections of (49a–d) rise along the hierarchy
theorem pairwise_flatten_patterns :
    ∀ bs ∈ [turkish, hiaki, korean, italian], bs.flatten.Pairwise (· < ·) := by
  decide

-- among (49a–d), only Italian puts Voice on the head of v
theorem exists_v_mem_voice_mem_iff : ∀ bs ∈ [turkish, hiaki, korean, italian],
    (∃ b ∈ bs, Projection.v ∈ b ∧ Projection.voice ∈ b) ↔ bs = italian := by
  decide

section Pattern

variable {bs : List (List Projection)} {b : List Projection} {x : Projection}

/-- A head bearing v and Voice bears every projection realized up to Voice, so an applicative or
a lower Caus has no head of its own. -/
theorem mem_of_v_mem_of_voice_mem (h : bs.flatten.Pairwise (· < ·)) (hb : b ∈ bs)
    (hv : Projection.v ∈ b) (hvoice : Projection.voice ∈ b) (hx : x ∈ bs.flatten)
    (hle : x ≤ .voice) : x ∈ b := by
  obtain ⟨b', hb', hxb'⟩ := List.mem_flatten.1 hx
  have hlt := (List.pairwise_flatten.1 h).2
  rcases List.Pairwise.forall_of_forall_of_flip
      (R := fun l₁ l₂ : List Projection ↦ l₁ = l₂ ∨ (∀ y ∈ l₁, ∀ z ∈ l₂, y < z) ∨
        ∀ y ∈ l₂, ∀ z ∈ l₁, y < z)
      (fun _ _ ↦ .inl rfl) (hlt.imp fun h ↦ .inr (.inl h)) (hlt.imp fun h ↦ .inr (.inr h))
      hb' hb with rfl | h | h
  · exact hxb'
  · exact absurd (h x hxb' .v hv) (by cases x <;> decide)
  · exact absurd (h .voice hvoice x hxb') (not_lt.2 hle)

-- (24b-ii): a pattern with an applicative off the head of v has Voice off it too
theorem voice_notMem_of_appl_notMem (h : bs.flatten.Pairwise (· < ·)) (hb : b ∈ bs)
    (hv : Projection.v ∈ b) (hs : Projection.appl ∈ bs.flatten) (ha : Projection.appl ∉ b) :
    Projection.voice ∉ b :=
  fun hvoice ↦ ha (mem_of_v_mem_of_voice_mem h hb hv hvoice hs (by decide))

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

variable {fv : Finset Feature} {ρ ρ' : Root}

/-- The terminal of a head, bearing the features of its projections, where the verbalizer bears
`fv` besides [+v]. -/
def terminal (fv : Finset Feature) (b : List Projection) : Terminal :=
  (b.toFinset.biUnion (·.features fv)).map .inl

@[simp] theorem inl_mem_terminal {f : Feature} :
    Sum.inl f ∈ terminal fv b ↔ ∃ y ∈ b, f ∈ y.features fv := by
  simp [terminal]

@[simp] theorem inr_notMem_terminal : Sum.inr ρ ∉ terminal fv b := by simp [terminal]

@[simp] theorem inl_v_mem_terminal : Sum.inl Feature.v ∈ terminal fv b ↔ Projection.v ∈ b := by
  rw [inl_mem_terminal]
  refine ⟨fun ⟨y, hy, h⟩ ↦ ?_, fun h ↦ ⟨_, h, Finset.mem_insert_self _ _⟩⟩
  cases y <;> first | exact hy | simp [Projection.features] at h

/-- The string of terminals of a word: the root, then its heads from the lowest up. -/
def word (ρ : Root) (fv : Finset Feature) (bs : List (List Projection)) : List Terminal :=
  {.inr ρ} :: bs.map (terminal fv)

/-- The lexical causative allomorph of `ρ`, realizing [+v, +CAUS] next to `ρ`. -/
def lexicalItem (ρ : Root) : VocabularyItem (Feature ⊕ Root) Exponent :=
  ⟨{(0, .inl .v), (0, .inl .caus), (-1, .inr ρ)}, .lexical ρ⟩

/-- (36): the elsewhere *-DIr*, realizing [+CAUS]. -/
def dirItem : VocabularyItem (Feature ⊕ Root) Exponent := {.inl .caus} ⟷ .dir

/-- Key's vocabulary for a root `ρ` with a lexical causative allomorph. -/
def vocabulary (ρ : Root) : RuleSet (VocabularyItem (Feature ⊕ Root) Exponent) :=
  [lexicalItem ρ, dirItem]

section Neighborhood

variable {n : Neighborhood Terminal}

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

end Neighborhood

/-- The exponents Key's vocabulary for `ρ` inserts along the word of the root `ρ'`, one for the
root and one for each head. -/
def exponents (ρ ρ' : Root) (fv : Finset Feature) (bs : List (List Projection)) :
    List (Option Exponent) :=
  (Neighborhood.along (word ρ' fv bs)).map (subsetPrinciple (vocabulary ρ))

@[simp] theorem length_exponents : (exponents ρ ρ' fv bs).length = bs.length + 1 := by
  simp [exponents, word]

private theorem getElem?_word_zero : (word ρ' fv bs)[0]? = some {.inr ρ'} := rfl

private theorem getElem?_word_succ (k : ℕ) :
    (word ρ' fv bs)[k + 1]? = bs[k]?.map (terminal fv) := by
  simp [word]

private theorem subsetPrinciple_around_word {k : ℕ} (hk : k ≤ bs.length) (b : List Projection) :
    subsetPrinciple (vocabulary ρ)
        (Neighborhood.around (word ρ' fv bs) (k + 1) (terminal fv b)) =
      if k = 0 ∧ ρ' = ρ ∧ Projection.v ∈ b ∧ ∃ y ∈ b, Feature.caus ∈ y.features fv then
        some (.lexical ρ)
      else if ∃ y ∈ b, Feature.caus ∈ y.features fv then some .dir else none := by
  have hk' : k < (word ρ' fv bs).length := by simp [word]; omega
  have hρ : Sum.inr ρ ∈ (word ρ' fv bs)[k] ↔ k = 0 ∧ ρ' = ρ := by
    rcases k with _ | k
    · simp only [word, List.getElem_cons_zero, Finset.mem_singleton, Sum.inr.injEq, true_and]
      exact eq_comm
    · simp [word]
  simp only [subsetPrinciple_vocabulary, applies_lexicalItem_iff, Neighborhood.focus_around,
    Neighborhood.nth_neg_one_around _ _ hk', hρ, inl_v_mem_terminal]
  simp only [inl_mem_terminal]
  split_ifs <;> first | rfl | grind

/-- The lowest head is realized by the allomorph of the root when it bears [+v, +CAUS] and the
root has one. Every other head bearing [+CAUS] is realized by *-DIr*, whatever else it bundles
and whatever stands next to it. -/
theorem exponents_eq (ρ ρ' : Root) (fv : Finset Feature) (bs : List (List Projection)) :
    exponents ρ ρ' fv bs = none :: bs.mapIdx fun i b ↦
      if i = 0 ∧ ρ' = ρ ∧ Projection.v ∈ b ∧ ∃ y ∈ b, Feature.caus ∈ y.features fv then
        some (.lexical ρ)
      else if ∃ y ∈ b, Feature.caus ∈ y.features fv then some .dir else none := by
  refine List.ext_getElem? fun i ↦ ?_
  rcases i with _ | k
  · simp [exponents, Neighborhood.along, getElem?_word_zero, subsetPrinciple_vocabulary,
      applies_lexicalItem_iff]
  · simp only [exponents, Neighborhood.along, List.getElem?_map, List.getElem?_mapIdx,
      getElem?_word_succ, List.getElem?_cons_succ, Option.map_map]
    rcases h : bs[k]? with _ | b
    · rfl
    · simp only [Option.map_some, Function.comp_apply,
        subsetPrinciple_around_word (List.getElem?_eq_some_iff.1 h).1.le]

-- the allomorph of the root appears iff the lowest head bears v and [+CAUS]
theorem lexical_mem_exponents_iff : some (.lexical ρ) ∈ exponents ρ ρ fv bs ↔
    ∃ b ∈ bs.head?, Projection.v ∈ b ∧ ∃ y ∈ b, Feature.caus ∈ y.features fv := by
  rw [exponents_eq]
  rcases bs with _ | ⟨b, t⟩
  · simp
  · have ht : ∀ {F : ℕ → List Projection → Option Exponent},
        (∀ i b, F i b ≠ some (.lexical ρ)) → some (.lexical ρ) ∉ t.mapIdx F := fun hF h ↦ by
      obtain ⟨i, hi, h⟩ := List.mem_mapIdx.1 h
      exact hF _ _ h
    rw [List.mapIdx_cons]
    simp only [List.mem_cons, reduceCtorEq, false_or, List.head?_cons, Option.mem_def,
      Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun ⟨hv, hc⟩ ↦ .inl (by simp [hv, hc])⟩
    rintro (h | h)
    · split_ifs at h with h1 <;> simp_all
    · exact absurd h (ht fun i b' h' ↦ by split_ifs at h' <;> simp_all)

end Pattern

/-! ### The patterns under Key's vocabulary -/

section Words

variable (ρ : Root) {ρ' : Root}

-- (49a): *-DIr* at the lower Caus, whatever the root
theorem exponents_turkish : exponents ρ ρ' ∅ turkish = [none, none, some .dir, none] := by
  simp [exponents_eq, List.mapIdx_cons, turkish, Projection.features]

-- a lexical causative under the productive one: the allomorph of the root, then *-DIr*
theorem exponents_turkish_caus :
    exponents ρ ρ {.caus} turkish = [none, some (.lexical ρ), some .dir, none] := by
  simp [exponents_eq, List.mapIdx_cons, turkish, Projection.features]

/-- A structure that expresses the causative feature on v and at both causative projections, each
on a head of its own, has *-DIr* at all three when its root has no allomorph. -/
theorem exponents_hiaki_caus (h : ρ' ≠ ρ) : exponents ρ ρ' {.caus} hiaki =
    [none, some .dir, none, some .dir, none, some .dir] := by
  simp [exponents_eq, List.mapIdx_cons, hiaki, Projection.features, h]

-- (49c): the head bundling Voice with the upper Caus is realized by *-DIr*
theorem exponents_korean : exponents ρ ρ' ∅ korean = [none, none, none, some .dir] := by
  simp [exponents_eq, List.mapIdx_cons, korean, Projection.features]

end Words

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

/-- The projections a causative structure realizes, from the root up: v, Voice and the position
of Cause. -/
def spine : Layer → Spine Projection
  | .root => ⟨[.v, .voice]⟩
  | .verb => ⟨[.v, .caus₁, .voice]⟩
  | .phase => ⟨[.v, .voice, .caus₂]⟩

/-- The pattern of a causative head: the position of Cause and Voice are on one head when the two
are bundled, and every other projection is on a head of its own. -/
def pattern (c : CauseHead) : List (List Projection) :=
  (spine c.selects).heads.splitBy fun x y ↦
    c.bundled && decide ((x = .voice ∨ y = .voice) ∧
      (x = causPosition c.selects ∨ y = causPosition c.selects))

variable (c : CauseHead)

theorem flatten_pattern : (pattern c).flatten = (spine c.selects).heads :=
  List.flatten_splitBy _ _

-- the projections of a causative structure rise along the hierarchy
theorem pairwise_flatten_pattern : (pattern c).flatten.Pairwise (· < ·) := by
  rw [flatten_pattern]
  obtain ⟨_ | _ | _, _ | _⟩ := c <;> decide

-- Cause is bundled with Voice iff its position is on the head of Voice
theorem exists_voice_mem_causPosition_mem_iff :
    (∃ b ∈ pattern c, Projection.voice ∈ b ∧ causPosition c.selects ∈ b) ↔ c.bundled = true := by
  obtain ⟨_ | _ | _, _ | _⟩ := c <;> decide

-- the verb-selecting Cause that is not bundled with Voice has the pattern (49a)
theorem pattern_verb : pattern ⟨.verb, false⟩ = turkish := by decide

/-- A causative head has a causee position iff its pattern puts v and Voice on different heads. -/
theorem hasCauseePosition_iff :
    c.HasCauseePosition ↔ ¬ ∃ b ∈ pattern c, Projection.v ∈ b ∧ Projection.voice ∈ b := by
  obtain ⟨_ | _ | _, _ | _⟩ := c <;>
    simp [Pylkkanen2008.hasCauseePosition_iff] <;> decide

-- under Key's vocabulary only a root-selecting Cause is realized by an allomorph of the root
theorem lexical_mem_exponents_pattern_iff (ρ : Root) :
    some (.lexical ρ) ∈ exponents ρ ρ (vFeatures c.selects) (pattern c) ↔ c.selects = .root := by
  rw [lexical_mem_exponents_iff]
  obtain ⟨_ | _ | _, _ | _⟩ := c <;> decide

end CauseHead

/-! ### Jung's Hiaki applicatives -/

/-- The classes of verb the chapter sorts its causatives by. -/
inductive Base where
  /-- An unaccusative verb. -/
  | unaccusative
  /-- An unergative verb. -/
  | unergative
  deriving DecidableEq, Repr

/-- The class of a Hiaki verb, by its gloss, as the chapter heads its examples. -/
def base? (gloss : List Char) : Option Base :=
  if gloss ∈ ["go".toList, "leave".toList] then some .unaccusative
  else if gloss ∈ ["jump".toList, "dance".toList, "speak".toList] then some .unergative
  else none

/-- The verb a row causativizes: the lexical gloss of the word bearing the causative. -/
def verb? (d : Datum) : Option (List Char) :=
  (d.glossedWords.find? fun w ↦ "CAUS".toList ∈ w.labels).bind (·.lexicalGloss?)

open Pylkkanen2008 in
/-- The layer the causative of a verb selects: the causative of an unaccusative is lexical, and
that of an unergative, whose external argument Voice introduces, selects a phase. -/
def selects : Base → Layer
  | .unaccusative => .root
  | .unergative => .phase

/-- (47), (48): an applicative outside a causative is acceptable iff Cause is expressed below the
applicative in the hierarchy. -/
theorem applicative_iff : ∀ d ∈ Examples.all, ∃ b ∈ (verb? d).bind base?,
    (d.judgment = .acceptable ↔ causPosition (selects b) < .appl) := by
  decide +kernel

end Harley2017
