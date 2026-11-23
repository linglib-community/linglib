module

public import Studies.Narrog2009
public import Studies.Narrog2010
public import Linglib.Data.Statistics.Narrog2012
public import Linglib.Syntax.Cartography
public import Linglib.Fragments.Japanese.Morph
public import Linglib.Morphology.Morphotactics.Template.Scale
public import Mathlib.Order.Antisymmetrization

/-!
# Narrog (2012): Modality, Subjectivity, and Semantic Change

[narrog-2012] orders the grammatical categories of the verbal clause by scope, from the embedding
behaviour of their markers in Modern Japanese ([narrog-2009a]), and hypothesizes that a change of
meaning leads from a category to one of the same or wider scope, and from a use to one of the
same or greater speech act orientation.

We define the categories of the combined hierarchy (`GramCategory`) and their preorder by scope
level (`GramCategory.scopeLevel`); categories on one level embed each other and are equivalent.
A non-modal category is a potential source of modality when some modal category lies at or above
it, and a potential target when some modal category lies at or below it
(`GramCategory.IsSource`, `GramCategory.IsTarget`). These are the columns of the book's table of
source and target categories (`GramCategory.isSource_iff`, `GramCategory.isTarget_iff`): voice
and benefactives are sources only, mood and illocutionary modification targets only, and aspect,
tense and negation, which share their levels with modal categories, both. A source lies
strictly below a category that is only a target (`source_lt_target`).

The book gives a hierarchy for each side of volitivity, in which the modal categories of the
other side do not appear (`GramCategory.nonVolitiveRow`, `GramCategory.volitiveRow`). The
combined hierarchy restricts to the non-volitive one, and to the volitive one except that it
separates negation from tense (`GramCategory.nonVolitiveRow_le_iff`,
`GramCategory.volitiveRow_le_iff`).

The modal categories are classes of the markers whose scope [narrog-2009a] tabulates, and a
hierarchy reads as an assignment of stretches of a scale in the sense of `Narrog2009.Represents`:
a marker at the row of its category, a tested category on a stretch ending at its row. Read so,
each of the two hierarchies represents the data on its side of volitivity
(`exists_represents_row`), and on the non-volitive side the rows of aspect, negation and tense
are the only ones that do (`snd_eq_of_represents_nonVolitiveRow`). The combined hierarchy does
not: it puts valuative obligation on the row of epistemic possibility, and no stretch for
internal negation separates the two (`not_represents_of_beki_eq_kaMoSirenai`,
`not_represents_scopeLevel`).

The suffix positions of the Japanese verb ascend along the hierarchy away from the stem
(`suffixesAscend_slotCategory`).

The three evidential categories lie on three levels, each at or below tense, so no monotone map
into the hierarchy of [cinque-1999] sends one of them to its evidential mood and tense to its
past tense (`not_monotone_of_moodEvidential`), and no placement on that hierarchy, which assigns
points, represents the data (`not_represents_cartography`).

The book classifies the changes of modal meaning tabulated in `Narrog2010.changes` by the sides
of volitivity they run between. Its four totals follow from that table (`gramsBetween_eq`), and
so do the two tendencies it reads off the classification: a change from a non-volitive to a
volitive meaning has its target in mood or its source in circumstantial possibility, and a
change from a volitive to a non-volitive meaning has an epistemic target.

## Implementation notes

The scope levels are the rows of the book's combined hierarchy. Stative and completive aspect,
which [narrog-2009a] tests, are taken to be the perfective and imperfective aspect of the
hierarchy, which stands in their place in it; phasal aspect, voice and benefactives come from a
later study and are not in that data. Possession, directionals and the
two kinds of honorification, which the table of source and target categories also lists, are not
in the hierarchy and are left out.

The book treats speech act orientation as a continuum on which a modal category covers a range
of positions, and places no category at a point, so no orientation is assigned to a category.
Its synopsis figure draws each tabulated change as an arrow on the map; those positions are not
encoded, and `minOrientation` records only that mood lies above modality proper.

## References

* [narrog-2012]
* [narrog-2010]
* [narrog-2009a]
* [cinque-1999]
-/

@[expose] public section

namespace Narrog2012

/-- Speech act orientation at the three positions labelled on the vertical axis of the book's
semantic map. The book treats the dimension as gradual and open-ended. -/
inductive SpeechActOrientation where
  /-- The modal judgment concerns conditions on the described event and its participants. -/
  | eventOriented
  /-- The modal judgment is the speaker's own at the time of speech. -/
  | speakerOriented
  /-- The use is tied to the speech act itself, including the hearer and the discourse. -/
  | speechActOriented
  deriving DecidableEq, Fintype, Repr

namespace SpeechActOrientation

instance : LinearOrder SpeechActOrientation :=
  LinearOrder.lift' SpeechActOrientation.ctorIdx (by decide)

instance : BoundedOrder SpeechActOrientation where
  top := speechActOriented
  le_top := by decide
  bot := eventOriented
  bot_le := by decide

end SpeechActOrientation

/-- Table 3.7: the categories of the combined scope hierarchy of Modern Japanese. A modal
category with a number is one of several of its kind on different levels. -/
inductive GramCategory where
  | voice
  | benefactive
  | phasalAspect
  | dynamicModality
  | boulomaicModality
  /-- Perfective and imperfective aspect. -/
  | perfImperfAspect
  /-- Deontic necessity. -/
  | deontic1
  /-- Predictive appearance. -/
  | evidentiality1
  /-- Internal negation. -/
  | negation
  /-- Epistemic necessity and expectation. -/
  | epistemic1
  /-- Inferential evidentiality. -/
  | evidentiality2
  | tense
  /-- Valuative obligation and recommendation. -/
  | deontic2
  /-- Epistemic possibility. -/
  | epistemic2
  /-- Reportive evidentiality. -/
  | evidentiality3
  /-- Speculative modality and epistemic mood. -/
  | epistemic3
  /-- The imperative and hortative moods. -/
  | volitiveMood
  | illocutionaryMod
  deriving DecidableEq, Fintype, Repr

namespace GramCategory

/-- Table 3.7: the row of a category in the combined hierarchy, counted from the bottom. -/
def scopeLevel : GramCategory → ℕ
  | voice | benefactive => 0
  | phasalAspect | dynamicModality | boulomaicModality => 1
  | perfImperfAspect | deontic1 | evidentiality1 => 2
  | negation | epistemic1 | evidentiality2 => 3
  | tense | deontic2 | epistemic2 | evidentiality3 => 4
  | epistemic3 => 5
  | volitiveMood => 6
  | illocutionaryMod => 7

/-- Categories are compared by scope level. -/
instance : Preorder GramCategory := Preorder.lift scopeLevel

instance : DecidableLE GramCategory := fun a _ ↦ inferInstanceAs (Decidable (a.scopeLevel ≤ _))
instance : DecidableLT GramCategory := fun a _ ↦ inferInstanceAs (Decidable (a.scopeLevel < _))

/-- The categories of modality proper. -/
def IsModal : GramCategory → Prop
  | dynamicModality | boulomaicModality | deontic1 | deontic2 | epistemic1 | epistemic2
  | epistemic3 | evidentiality1 | evidentiality2 | evidentiality3 => True
  | _ => False

instance : DecidablePred IsModal := fun c ↦ by cases c <;> unfold IsModal <;> infer_instance

/-- A non-modal category is a potential source of modality when some modal category has the
same or wider scope. -/
def IsSource (c : GramCategory) : Prop := ¬ c.IsModal ∧ ∃ m : GramCategory, m.IsModal ∧ c ≤ m

/-- A non-modal category is a potential target of modality when some modal category has the
same or narrower scope. -/
def IsTarget (c : GramCategory) : Prop := ¬ c.IsModal ∧ ∃ m : GramCategory, m.IsModal ∧ m ≤ c

instance : DecidablePred IsSource := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred IsTarget := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- Table 3.10: the potential sources of modality are voice, benefactives, aspect, tense and
negation. -/
theorem isSource_iff (c : GramCategory) : c.IsSource ↔
    c ∈ [voice, benefactive, phasalAspect, perfImperfAspect, negation, tense] := by
  cases c <;> decide

-- Table 3.10: the potential targets are aspect, tense, negation, mood and illocutionary
-- modification.
theorem isTarget_iff (c : GramCategory) : c.IsTarget ↔
    c ∈ [phasalAspect, perfImperfAspect, negation, tense, volitiveMood, illocutionaryMod] := by
  cases c <;> decide

theorem deontic1_lt_epistemic1 : deontic1 < epistemic1 := by decide

theorem dynamicModality_lt_deontic1 : dynamicModality < deontic1 := by decide

-- Mood and illocutionary modification outscope every category of modality proper.
theorem lt_volitiveMood_of_isModal {c : GramCategory} (hc : c.IsModal) : c < volitiveMood := by
  cases c <;> first | decide | exact hc.elim

-- Voice markers become modal markers and not the reverse (section 4.6).
theorem voice_lt_of_isModal {c : GramCategory} (hc : c.IsModal) : voice < c := by
  cases c <;> first | decide | exact hc.elim

-- Aspect and event-oriented modality embed each other, so change is possible in both directions
-- (section 7.3.1).
theorem antisymmRel_aspect :
    AntisymmRel (· ≤ ·) phasalAspect dynamicModality ∧
    AntisymmRel (· ≤ ·) phasalAspect boulomaicModality ∧
    AntisymmRel (· ≤ ·) perfImperfAspect deontic1 := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

theorem volitiveMood_lt_illocutionaryMod : volitiveMood < illocutionaryMod := by decide

theorem le_illocutionaryMod (c : GramCategory) : c ≤ illocutionaryMod := by
  cases c <;> decide

theorem evidentiality_le_tense :
    evidentiality1 < tense ∧ evidentiality2 < tense ∧ evidentiality3 ≤ tense := by
  decide

/-! ### The hierarchies of the two sides of volitivity -/

/-- Table 3.5: the row of a category in the hierarchy with non-volitive modalities, counted from
the bottom; the volitive categories are not in it. -/
def nonVolitiveRow : GramCategory → Option ℕ
  | voice | benefactive => some 0
  | phasalAspect | dynamicModality => some 1
  | perfImperfAspect | evidentiality1 => some 2
  | negation | epistemic1 | evidentiality2 => some 3
  | tense | epistemic2 | evidentiality3 => some 4
  | epistemic3 => some 5
  | illocutionaryMod => some 6
  | boulomaicModality | deontic1 | deontic2 | volitiveMood => none

/-- Table 3.6: the row of a category in the hierarchy with volitive modalities, counted from the
bottom; the non-volitive modal categories are not in it. -/
def volitiveRow : GramCategory → Option ℕ
  | voice | benefactive => some 0
  | phasalAspect | boulomaicModality => some 1
  | perfImperfAspect | deontic1 => some 2
  | tense | negation | deontic2 => some 3
  | volitiveMood => some 4
  | illocutionaryMod => some 5
  | dynamicModality | epistemic1 | epistemic2 | epistemic3 | evidentiality1 | evidentiality2
  | evidentiality3 => none

-- On the categories of Table 3.5 the combined hierarchy is that table's.
theorem nonVolitiveRow_le_iff (a b : GramCategory) :
    ∀ i ∈ nonVolitiveRow a, ∀ j ∈ nonVolitiveRow b, (i ≤ j ↔ a ≤ b) := by
  cases a <;> cases b <;> decide

-- On the categories of Table 3.6 the combined hierarchy differs from it only in separating
-- negation from tense, which share a row there.
theorem volitiveRow_le_iff (a b : GramCategory) :
    ∀ i ∈ volitiveRow a, ∀ j ∈ volitiveRow b, (i ≤ j ↔ a ≤ b ∨ b = negation ∧ a ≤ tense) := by
  cases a <;> cases b <;> decide

theorem isSome_nonVolitiveRow_or_volitiveRow (c : GramCategory) :
    (nonVolitiveRow c).isSome ∨ (volitiveRow c).isSome := by
  cases c <;> decide

-- A modal category belongs to exactly one of the two hierarchies.
theorem isSome_nonVolitiveRow_iff_of_isModal {c : GramCategory} (hc : c.IsModal) :
    (nonVolitiveRow c).isSome ↔ ¬ (volitiveRow c).isSome := by
  cases c <;> first | decide | exact hc.elim

end GramCategory

open GramCategory

-- A potential source of modality has narrower scope than a category that is only a potential
-- target.
theorem source_lt_target {c d : GramCategory} (hc : c.IsSource) (hd : d.IsTarget)
    (hd' : ¬ d.IsSource) : c < d := by
  obtain ⟨-, m, hm, hcm⟩ := hc
  have hmd : ¬ d.scopeLevel ≤ m.scopeLevel := fun h ↦ hd' ⟨hd.1, m, hm, h⟩
  exact Nat.lt_of_le_of_lt hcm (Nat.lt_of_not_le hmd)

/-- No monotone map into Cinque's hierarchy sends a category at or below tense to the evidential
mood and tense to the past tense. -/
theorem not_monotone_of_moodEvidential {f : GramCategory → Cartography.Head} {e : GramCategory}
    (he : e ≤ tense) (hf : f e = .moodEvidential) (ht : f tense = .tPast) : ¬ Monotone f :=
  fun h ↦ absurd (hf ▸ ht ▸ h he) (by decide)

/-! ### The embedding data of [narrog-2009a] -/

/-- The category of the hierarchy that a marker of [narrog-2009a] represents, as that study's
figures of the two layerings label them. -/
def _root_.Narrog2009.Marker.gramCategory : Narrog2009.Marker → GramCategory
  | .eru | .rareru | .kotoGaDekiru => dynamicModality
  | .soo1 => evidentiality1
  | .tai | .teHosii => boulomaicModality
  | .nakerebaNaranai => deontic1
  | .rebaIi | .beki => deontic2
  | .hazu => epistemic1
  | .yoo | .rasii => evidentiality2
  | .kaMoSirenai => epistemic2
  | .soo2 => evidentiality3
  | .daroo => epistemic3
  | .hortative | .imperativeI | .imperativeII => volitiveMood

/-- The category of the hierarchy that a category tested in [narrog-2009a] corresponds to.
External negation and nominalization have none. -/
def _root_.Narrog2009.Category.gramCategory : Narrog2009.Category → Option GramCategory
  | .stativeAspect | .completiveAspect => some perfImperfAspect
  | .internalNegation => some negation
  | .tense => some tense
  | .illocutionaryModulation => some illocutionaryMod
  | .externalNegation | .nominalization => none

/-- The point of a marker under a table of rows: the row of its category. -/
def _root_.Narrog2009.Marker.point (row : GramCategory → Option ℕ) (m : Narrog2009.Marker) : ℕ :=
  (row m.gramCategory).getD 0

open Narrog2009 (Represents) in
/-- Each of the two hierarchies represents the embedding data of [narrog-2009a] on its side of
volitivity, with every marker at the row of its category and every tested category on a stretch
that ends at its row. -/
theorem exists_represents_row :
    (∃ g : Narrog2009.Category → NonemptyInterval ℕ,
      (∀ c, ∀ x ∈ c.gramCategory, nonVolitiveRow x = some (g c).snd) ∧
      Represents {m | ¬ m.IsVolitive} {c | c.gramCategory.isSome}
        (fun m ↦ .pure (m.point nonVolitiveRow)) g) ∧
    ∃ g : Narrog2009.Category → NonemptyInterval ℕ,
      (∀ c, ∀ x ∈ c.gramCategory, volitiveRow x = some (g c).snd) ∧
      Represents {m | m.IsVolitive} {c | c.gramCategory.isSome}
        (fun m ↦ .pure (m.point volitiveRow)) g := by
  refine ⟨⟨fun c ↦ match c with
      | .stativeAspect | .completiveAspect => ⟨(1, 2), by decide⟩
      | .internalNegation => ⟨(1, 3), by decide⟩
      | .tense => ⟨(3, 4), by decide⟩
      | _ => ⟨(6, 6), by decide⟩, ?_, ?_⟩,
    fun c ↦ match c with
      | .stativeAspect | .completiveAspect => ⟨(1, 2), by decide⟩
      | .internalNegation | .tense => ⟨(1, 3), by decide⟩
      | _ => ⟨(5, 5), by decide⟩, ?_, ?_⟩
  · intro c; cases c <;> decide
  · intro m hm c hc; revert hm hc; cases m <;> cases c <;> decide
  · intro c; cases c <;> decide
  · intro m hm c hc; revert hm hc; cases m <;> cases c <;> decide

open Narrog2009 (Represents) in
/-- On the non-volitive side the rows of aspect, negation and tense are forced: in any
representation with the markers at the rows of their categories, the stretch of each ends at its
row. -/
theorem snd_eq_of_represents_nonVolitiveRow {g : Narrog2009.Category → NonemptyInterval ℕ}
    (h : Represents {m | ¬ m.IsVolitive} {c | c.gramCategory.isSome}
      (fun m ↦ .pure (m.point nonVolitiveRow)) g) {c : Narrog2009.Category}
    (hc : c ∈ [.stativeAspect, .completiveAspect, .internalNegation, .tense]) :
    ∀ x ∈ c.gramCategory, nonVolitiveRow x = some (g c).snd := by
  have key : ∀ {c : Narrog2009.Category} {n : ℕ}, (NonemptyInterval.pure n).Overlaps (g c) →
      (g c).Precedes (.pure (n + 1)) → ∀ x ∈ c.gramCategory, some n = some (g c).snd :=
    fun ho hp _ _ ↦ congrArg some (le_antisymm ho.1 (Nat.le_of_lt_succ hp))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> intro x hx <;> cases hx
  · exact key (n := 2) (h .soo1 (by decide) .stativeAspect rfl)
      (h .hazu (by decide) .stativeAspect rfl) _ rfl
  · exact key (n := 2) (h .soo1 (by decide) .completiveAspect rfl)
      (h .hazu (by decide) .completiveAspect rfl) _ rfl
  · exact key (n := 3) (h .hazu (by decide) .internalNegation rfl)
      (h .kaMoSirenai (by decide) .internalNegation rfl) _ rfl
  · exact key (n := 4) (h .kaMoSirenai (by decide) .tense rfl)
      (h .daroo (by decide) .tense rfl) _ rfl

open Narrog2009 (Represents) in
/-- No assignment of points that puts *beki* and *ka mo sirenai* together, as the combined
hierarchy puts valuative obligation and epistemic possibility on one row, represents the data:
*beki* overlaps internal negation and *ka mo sirenai* lies above it. -/
theorem not_represents_of_beki_eq_kaMoSirenai {β : Type*} [LinearOrder β]
    {p : Narrog2009.Marker → β} (hp : p .beki = p .kaMoSirenai)
    (g : Narrog2009.Category → NonemptyInterval β) :
    ¬ Represents Set.univ {c | c.gramCategory.isSome} (fun m ↦ .pure (p m)) g := by
  intro h
  have h₁ : (NonemptyInterval.pure (p .beki)).Overlaps (g .internalNegation) :=
    h .beki trivial .internalNegation rfl
  have h₂ : (g .internalNegation).Precedes (.pure (p .kaMoSirenai)) :=
    h .kaMoSirenai trivial .internalNegation rfl
  exact not_lt_of_ge (hp ▸ h₁.1) h₂

theorem not_represents_scopeLevel (g : Narrog2009.Category → NonemptyInterval ℕ) :
    ¬ Narrog2009.Represents Set.univ {c | c.gramCategory.isSome}
      (fun m ↦ .pure m.gramCategory.scopeLevel) g :=
  not_represents_of_beki_eq_kaMoSirenai (p := fun m ↦ m.gramCategory.scopeLevel) rfl g

-- A hierarchy of heads assigns points, so no placement of the markers and categories on
-- Cinque's hierarchy represents the data.
theorem not_represents_cartography (h : Narrog2009.Marker → Cartography.Head)
    (h' : Narrog2009.Category → Cartography.Head) :
    ¬ Narrog2009.Represents Set.univ Set.univ (fun m ↦ .pure (h m)) fun c ↦ .pure (h' c) :=
  Narrog2009.not_represents_pure trivial trivial trivial trivial h h'

/-! ### Morpheme order -/

/-- The category of the hierarchy that a suffix position of the Japanese verb expresses: the
passive, the desiderative *-tai*, the negative and the final inflection, read as tense. -/
def slotCategory : Japanese.Verb.Slot → Option GramCategory
  | .voice => some voice
  | .desiderative => some boulomaicModality
  | .negation => some negation
  | .inflection => some tense
  | .derivation | .valence | .politeness => none

-- The order of the suffixes reflects scope.
theorem suffixesAscend_slotCategory : Japanese.Verb.template.SuffixesAscend slotCategory := by
  decide

/-! ### The changes of [narrog-2010] -/

/-- The lowest position a use at a point of the map of [narrog-2010] can take: the directive
moods lie at the speech act-oriented end, and modality proper and the future reach down to the
event-oriented pole. -/
def minOrientation (p : Narrog2010.Point) : SpeechActOrientation :=
  if p.IsMood then ⊤ else ⊥

theorem minOrientation_source_le_target :
    ∀ c ∈ Narrog2010.changes, ∀ p ∈ c.source.meaning, ∀ q ∈ c.target.meaning,
      minOrientation p ≤ minOrientation q := by
  decide

/-- The grams of the changes of [narrog-2010] that run from side `v` of volitivity to side `w`. -/
def gramsBetween (v w : Prop) [Decidable v] [Decidable w] : ℕ :=
  ((Narrog2010.changes.filter fun c ↦ (∀ p ∈ c.source.meaning, p.IsVolitive ↔ v) ∧
    ∀ p ∈ c.target.meaning, p.IsVolitive ↔ w).map (·.grams)).sum

-- The four totals of the book's classification of the changes by volitivity follow from the
-- table of [narrog-2010] and the volitivity of its meanings.
theorem gramsBetween_eq :
    gramsBetween False True = nonVolitiveToVolitive ∧
    gramsBetween False False = withinNonVolitive ∧
    gramsBetween True False = volitiveToNonVolitive ∧
    gramsBetween True True = withinVolitive := by
  decide

-- A change from a non-volitive to a volitive meaning has its target in mood or its source in
-- circumstantial possibility (section 5.2).
theorem isMood_or_circumstantial_of_toVolitive :
    ∀ c ∈ Narrog2010.changes,
      (∀ p ∈ c.source.meaning, ¬ p.IsVolitive) → (∀ p ∈ c.target.meaning, p.IsVolitive) →
      (∀ p ∈ c.target.meaning, p.IsMood) ∨
        ∀ p ∈ c.source.meaning, p = .modal (.possibility, .circumstantial) := by
  decide

-- A change from a volitive to a non-volitive meaning has an epistemic target (section 5.2).
theorem epistemic_of_toNonVolitive :
    ∀ c ∈ Narrog2010.changes,
      (∀ p ∈ c.source.meaning, p.IsVolitive) → (∀ p ∈ c.target.meaning, ¬ p.IsVolitive) →
      ∀ p ∈ c.target.meaning, ∃ fo, p = .modal (fo, .epistemic) := by
  decide

end Narrog2012
