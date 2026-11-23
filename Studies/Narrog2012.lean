module

public import Studies.Narrog2010
public import Linglib.Data.Statistics.Narrog2012
public import Linglib.Syntax.Cartography
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

The three evidential categories lie on three levels, each at or below tense, so no monotone map
into the hierarchy of [cinque-1999] sends one of them to its evidential mood and tense to its
past tense (`not_monotone_of_moodEvidential`).

The book classifies the changes of modal meaning tabulated in `Narrog2010.changes` by the sides
of volitivity they run between. Its four totals follow from that table (`gramsBetween_eq`), and
so do the two tendencies it reads off the classification: a change from a non-volitive to a
volitive meaning has its target in mood or its source in circumstantial possibility, and a
change from a volitive to a non-volitive meaning has an epistemic target.

## Implementation notes

The scope levels are the rows of the book's combined hierarchy. Possession, directionals and the
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

/-- On the categories of the hierarchy with volitive modalities, the combined hierarchy differs
from it only in separating negation from tense, which share a row there. -/
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

/-- A potential source of modality has narrower scope than a category that is only a potential
target. -/
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

/-- The four totals of the book's classification of the changes by volitivity follow from the
table of [narrog-2010] and the volitivity of its meanings. -/
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
