module

public import Linglib.Fragments.English.TemporalDeictic
public import Linglib.Fragments.Greek.StandardModern.TemporalDeictic
public import Linglib.Fragments.Hebrew.TemporalDeictic
public import Linglib.Fragments.Japanese.TemporalDeictic
public import Linglib.Fragments.Slavic.Russian.TemporalDeictic
public import Linglib.Data.Examples.TsiliaZhao2026

/-!
# Tsilia and Zhao (2026): Tense and Perspective: A Solution to the ⌈then⌉-Present Puzzle

This file formalizes the solution of [tsilia-zhao-2026] to the ⌈then⌉-present puzzle, (12):
the temporal adverb ⌈then⌉ cannot restrict a present-tensed verb phrase, whether the present
is shifted or not. In Greek, Hebrew, Russian and Japanese a present under a past attitude
verb shifts to the attitude's time, (8), yet ⌈then⌉ is still excluded, (9)–(11), although it
restricts an embedded past with the same simultaneous reference, (38)–(39), and a deleted,
sequence-of-tense past, (48)–(49). Tenses and ⌈then⌉ are temporal pronouns with
presuppositions relative to a perspective parameter `π`, (69)–(71): PRES overlap, PAST
precedence, ⌈then⌉ disjointness, the substrate's `Tense.Perspective.Presup` at the cells
`present`, `past` and `presentᶜ`. Tense shift is the rebinding of `π`, by the propositional
operator OP_π of (73), to an evaluation index that an attitude verb or WOLL binds, so a
clausemate PRES and ⌈then⌉ shift together and read the same `π`; since ⌈then⌉ restricts the
reference of the tense it modifies, (76), their presuppositions clash whatever `π` is,
`not_restricted_present`, the derivations (77), (79), (81) and (82), and so for each adverb of
the sample, `not_restricted_present_of_mem`. A pronominal anchor would let the two anchor
separately, (36), which is coherent, `exists_split_anchor`, hence the parameter. ⌈then⌉
restricts a PAST to its own reference, `restricted_past_self`, and a deleted tense, carrying no
presupposition, (86)–(87), is compatible with ⌈then⌉ when no operator shifts the perspective
onto its reference, (89), `restricted_top_of_not_overlaps` and `not_restricted_top_of_le`.
Japanese *tooji* is past-oriented and so, unlike *then*, excluded of a future time, (32),
`presup_then_not_tooji_of_precedes`. Russian *sejčas* 'now' has the presupposition of PRES,
(115), and restricts a present, `restricted_present_sejchas`.

## Implementation notes

Times are closed intervals of a linear order, and clause meanings are their presuppositions
as functions of the perspective; the assertion, the assignment and the evaluation index are
suppressed, so OP_π is instantiation of the perspective, and the intensional binding that
licenses a shift, absent in relative clauses under past except in Japanese, is described by
the rows. The typology of Tables 1 and 2 is the rows: under past the present shifts in
attitude reports in Greek, Hebrew, Russian and Japanese, in relative clauses only in
Japanese, and never in English, whose present under past indicates the utterance time; under
future it shifts everywhere, WOLL binding the index, and only English admits ⌈then⌉ there,
its present being deleted under WOLL's PRES rather than shifted, a difference among
sequence-of-tense languages the paper leaves open, (94)–(97). The perspective is not the
context's time, since Greek shifts the present but never *tora* 'now', (99). The examples are
the rows of `Data.Examples.TsiliaZhao2026`.

## TODO

The paper derives the exclusion of *sejčas* from a simultaneous embedded past, (112), from the
presuppositions (114) and (115) "just like the ⌈then⌉-present puzzle". Containment and the two
presuppositions are jointly satisfiable, `exists_restricted_past_present`, because precedence,
unlike overlap, does not pass to a containing time; the exclusion follows once the reference of
*sejčas* lies within the perspective, `not_restricted_past_of_le`, an assumption the paper does
not state.

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

/-- The ⌈then⌉ adverbs of the paper's sample. -/
def thenAdverbs : List DeicticAdverb :=
  [English.TemporalDeictic.then_, Greek.StandardModern.TemporalDeictic.tote,
    Hebrew.TemporalDeictic.az, Russian.TemporalDeictic.togda, Japanese.TemporalDeictic.tooji]

/-- No adverb of the sample restricts a present tense, the ⌈then⌉-present puzzle (12). -/
theorem not_restricted_present_of_mem {a : DeicticAdverb} (ha : a ∈ thenAdverbs)
    (r th π : NonemptyInterval T) : ¬ Restricted ⟦present⟧ a.cell r th π :=
  not_restricted_present ((by decide : ∀ a ∈ thenAdverbs, a.IsDistal) a ha) r th π

/-- The clash is the adverb's doing: Russian *sejčas* 'now', with the presupposition of PRES,
(115), restricts a present tense. -/
theorem restricted_present_sejchas (r : NonemptyInterval T) :
    Restricted ⟦present⟧ Russian.TemporalDeictic.sejchas.cell r r r :=
  ⟨presup_present.2 (NonemptyInterval.overlaps_refl r), le_rfl,
    presup_present.2 (NonemptyInterval.overlaps_refl r)⟩

/-- With pronominal anchors, PRES and ⌈then⌉ could take different times and the clause would be
coherent (36). -/
theorem exists_split_anchor {π₁ π₂ : NonemptyInterval T} (h : ¬ π₁.Overlaps π₂) :
    ∃ r th, Presup ⟦present⟧ π₁ r ∧ r ≤ th ∧ Presup ⟦present⟧ᶜ π₂ th :=
  ⟨π₁, π₁, presup_present.2 (NonemptyInterval.overlaps_refl π₁), le_rfl,
    presup_compl_present.2 h⟩

/-! ### Past and deleted tense (sections 3 and 6) -/

/-- (38), (39), (44): a PAST admits at its own reference any adverb whose cell admits
precedence, ⌈then⌉ and *tooji* alike. -/
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
meeting is disjoint, and ⌈then⌉ restricts the deleted past. -/
theorem restricted_top_of_not_overlaps (h : ¬ r.Overlaps π) : Restricted ⊤ ⟦present⟧ᶜ r r π :=
  restricted_top_iff.2 ⟨le_rfl, presup_compl_present.2 h⟩

/-- With OP_π shifting the perspective onto the time of the reported speech, a distal adverb cannot
restrict it (89b). -/
theorem not_restricted_top_of_le (hC : .eq ∉ C) (hr : r ≤ π) : ¬ Restricted ⊤ C r th π :=
  fun ⟨_, hle, hth⟩ ↦ not_presup_of_presup_present hC
    (presup_present.2 (NonemptyInterval.overlaps_of_le hr)) hle hth

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
