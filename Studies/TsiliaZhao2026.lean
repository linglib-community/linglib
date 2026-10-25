module

public import Linglib.Fragments.English.TemporalDeictic
public import Linglib.Fragments.Greek.StandardModern.TemporalDeictic
public import Linglib.Fragments.Hebrew.TemporalDeictic
public import Linglib.Fragments.Japanese.TemporalDeictic
public import Linglib.Fragments.Slavic.Russian.TemporalDeictic
public import Linglib.Data.Examples.TsiliaZhao2026

/-!
# Tsilia and Zhao (2026): Tense and perspective

The temporal adverb ⌜then⌝ cannot restrict a present tense, whether the present is shifted or not,
(12). Tenses and ⌜then⌝ are temporal pronouns presupposing a position relative to a perspective
`π`, (69)–(71): PRES overlap, PAST precedence and ⌜then⌝ disjointness, the substrate's
`Tense.Perspective.Presup` at the cells `present`, `past` and `presentᶜ`. The operator OP_π of
(73) rebinds `π` for a whole clause, so a clausemate tense and ⌜then⌝, which restricts the tense's
reference (76), read the same `π`, and a present clashes with ⌜then⌝ whatever `π` is. A deleted
tense carries no presupposition, (86)–(87).

## Main results

* `TsiliaZhao2026.not_restricted_present`: a distal adverb cannot restrict a present.
* `TsiliaZhao2026.accepted_iff_exists_restricted`: an example with ⌜then⌝ is accepted exactly
  when some perspective satisfies the presuppositions of its tense and its adverb.
* `TsiliaZhao2026.exists_split_anchor`: pronominal anchors would let a present and ⌜then⌝ anchor
  apart, (36), hence the parameter.

## Implementation notes

Times are closed intervals of a linear order, and clause meanings are their presuppositions as
functions of the perspective; the assertion, the assignment and the evaluation index are
suppressed, so OP_π is instantiation of the perspective, and whether a language shifts or deletes
a tense in a given environment, Tables 1 and 2, is read from the rows. An example's tense is its
embedded tense, or else its matrix tense, and is `⊤` when the paper analyses it as deleted, as the
English present under future, (90)–(93); its adverb is the ⌜then⌝ of its language.

## TODO

The paper derives the exclusion of *sejčas* from a simultaneous embedded past, (112), from the
presuppositions (114) and (115) "just like the ⌜then⌝-present puzzle". Containment and the two
presuppositions are jointly satisfiable, `exists_restricted_past_present`, because precedence,
unlike overlap, does not pass to a containing time; the exclusion follows once the reference of
*sejčas* lies within the perspective, `not_restricted_past_of_le`, an assumption the paper does
not state.

The rows record which tenses are deleted rather than deriving it from generalization (94), that a
sequence-of-tense language with a shiftable present cannot delete it. The argument of section 7
that the perspective is neither the context's time nor the index's, (98)–(104), with the unshifted
*tora* 'now' of (99), is not formalized.

## References

* [tsilia-zhao-2026]
* [zhao-2025]
* [ogihara-sharvit-2012]
* [anand-nevins-2004]
* [deal-2020]
* [abusch-1988]
* [heim-1992]
-/

@[expose] public section

namespace TsiliaZhao2026

open scoped Denotes

open Tense Tense.Perspective

variable {T : Type*} [LinearOrder T] {C : Finset Ordering} {r th π : NonemptyInterval T}

/-! ### The clash and the shift-together effect (section 5) -/

/-- (76)–(77): the presuppositions of a clause whose tense, with cell `tense` and reference `r`,
is modified by an adverb with cell `adv` and reference `th`, as a function of the perspective.
The silent *during* places the reference of the tense within that of the adverb. -/
def Restricted (tense adv : Finset Ordering) (r th π : NonemptyInterval T) : Prop :=
  Presup tense π r ∧ r ≤ th ∧ Presup adv π th

/-- A present-tensed clause modified by a distal adverb is contradictory whatever the perspective
((75), (78), (81)–(82)). -/
theorem not_restricted_present {a : DeicticAdverb} (ha : a.IsDistal)
    (r th π : NonemptyInterval T) : ¬ Restricted ⟦present⟧ a.cell r th π :=
  fun ⟨hr, hle, hth⟩ ↦ not_presup_of_presup_present ha hr hle hth

/-- The ⌜then⌝ adverbs of the paper's sample, by the Glottocode of their language. -/
def thenAdverbs : List (String × DeicticAdverb) :=
  [("stan1293", English.TemporalDeictic.then_),
    ("mode1248", Greek.StandardModern.TemporalDeictic.tote),
    ("hebr1245", Hebrew.TemporalDeictic.az), ("russ1263", Russian.TemporalDeictic.togda),
    ("nucl1643", Japanese.TemporalDeictic.tooji)]

/-- No adverb of the sample restricts a present tense, the ⌜then⌝-present puzzle (12). -/
theorem not_restricted_present_of_mem {a : DeicticAdverb} (ha : a ∈ thenAdverbs.map Prod.snd)
    (r th π : NonemptyInterval T) : ¬ Restricted ⟦present⟧ a.cell r th π :=
  not_restricted_present ((by decide : ∀ a ∈ thenAdverbs.map Prod.snd, a.IsDistal) a ha) r th π

/-- The clash is the adverb's doing: Russian *sejčas* 'now', with the presupposition of PRES,
(115), restricts a present tense. -/
theorem restricted_present_sejchas (r : NonemptyInterval T) :
    Restricted ⟦present⟧ Russian.TemporalDeictic.sejchas.cell r r r :=
  ⟨presup_present.2 (NonemptyInterval.overlaps_refl r), le_rfl,
    presup_present.2 (NonemptyInterval.overlaps_refl r)⟩

/-- With pronominal anchors, PRES and ⌜then⌝ could take different times and the clause would be
coherent (36). -/
theorem exists_split_anchor {π₁ π₂ : NonemptyInterval T} (h : ¬ π₁.Overlaps π₂) :
    ∃ r th, Presup ⟦present⟧ π₁ r ∧ r ≤ th ∧ Presup ⟦present⟧ᶜ π₂ th :=
  ⟨π₁, π₁, presup_present.2 (NonemptyInterval.overlaps_refl π₁), le_rfl,
    presup_compl_present.2 h⟩

/-! ### Past and deleted tense (sections 3 and 6) -/

/-- (38), (39), (44): a PAST admits at its own reference any adverb whose cell admits
precedence, ⌜then⌝ and *tooji* alike. -/
theorem restricted_past_self (hC : .lt ∈ C) (h : Presup ⟦past⟧ π r) : Restricted ⟦past⟧ C r r π :=
  ⟨h, le_rfl, h.mono (Finset.singleton_subset_iff.2 hC)⟩

/-- (32): *tooji* is used only of past times, so unlike English *then* it cannot refer to a time
after the perspective. -/
theorem presup_then_not_tooji_of_precedes (h : π.Precedes th) :
    Presup English.TemporalDeictic.then_.cell π th ∧
      ¬ Presup Japanese.TemporalDeictic.tooji.cell π th :=
  ⟨(presup_future.2 h).mono (by decide),
    fun h' ↦ NonemptyInterval.precedes_asymm h (presup_past.1 h')⟩

/-- (86)–(87): a deleted tense carries no presupposition, so only the adverb's remains. -/
theorem restricted_top_iff : Restricted ⊤ C r th π ↔ r ≤ th ∧ Presup C π th :=
  and_iff_right presup_top

/-- (89a): with no OP_π the perspective stays the utterance time, from which the reported
meeting is disjoint, and ⌜then⌝ restricts the deleted past. -/
theorem restricted_top_of_not_overlaps (h : ¬ r.Overlaps π) : Restricted ⊤ ⟦present⟧ᶜ r r π :=
  restricted_top_iff.2 ⟨le_rfl, presup_compl_present.2 h⟩

/-- With OP_π shifting the perspective onto the time of the reported speech, a distal adverb cannot
restrict it (89b). -/
theorem not_restricted_top_of_le (hC : .eq ∉ C) (hr : r ≤ π) : ¬ Restricted ⊤ C r th π :=
  fun ⟨_, hle, hth⟩ ↦ not_presup_of_presup_present hC
    (presup_present.2 (NonemptyInterval.overlaps_of_le hr)) hle hth

/-! ### The examples -/

/-- The cell of the tense an example's adverb restricts: its embedded tense, or else its matrix
tense, and `⊤` for a deleted tense. -/
def tenseCell (row : Datum) : Option (Finset Ordering) :=
  if row.feature? "shifted" = some "deleted" then some ⊤ else
    row.parse? (if (row.feature? "embedded").isSome then "embedded" else "matrix")
      [("present", ⟦present⟧), ("past", ⟦past⟧), ("future", ⟦future⟧), ("deleted past", ⊤)]

/-- The ⌜then⌝ of an example's language, if the example has one. -/
def adverb (row : Datum) : Option DeicticAdverb :=
  (row.feature? "then").bind fun _ ↦ thenAdverbs.lookup row.language

/-- An example with ⌜then⌝ is accepted, by some speakers at least, exactly when some perspective
satisfies the presuppositions of its tense and of the adverb restricting it. -/
theorem accepted_iff_exists_restricted [Nontrivial T] :
    ∀ row ∈ Examples.all, ∀ C ∈ tenseCell row, ∀ a ∈ adverb row,
      (.variable ≤ row.judgment ↔ ∃ π r th : NonemptyInterval T, Restricted C a.cell r th π) := by
  simp only [Restricted, exists_presup_iff]
  decide +kernel

/-! ### Perspective-sensitive *now* (section 7) -/

/-- (112), (114)–(115): a past reference cannot be restricted by a *sejčas* whose reference
lies within the perspective. -/
theorem not_restricted_past_of_le (hth : th ≤ π) : ¬ Restricted ⟦past⟧ C r th π :=
  fun ⟨hr, hle, _⟩ ↦ NonemptyInterval.precedes_not_overlaps (presup_past.1 hr)
    (NonemptyInterval.overlaps_of_le (hle.trans hth))

/-- The presuppositions (114) and (115) alone do not exclude a past under *sejčas*. -/
theorem exists_restricted_past_present {a b : T} (hab : a < b) :
    ∃ r th π : NonemptyInterval T, Restricted ⟦past⟧ ⟦present⟧ r th π :=
  ⟨.pure a, ⟨(a, b), hab.le⟩, .pure b, presup_past.2 (by exact hab),
    NonemptyInterval.le_def.2 ⟨le_rfl, hab.le⟩,
    presup_present.2 ⟨hab.le, le_rfl⟩⟩

end TsiliaZhao2026
