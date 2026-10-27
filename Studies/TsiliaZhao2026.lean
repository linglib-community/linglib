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
(12). Tenses and ⌜then⌝ are temporal pronouns presupposing a relation to a perspective `π`,
(69)–(71): PRES overlap, PAST precedence and ⌜then⌝ disjointness, the substrate's
`Tense.Perspective.Presup` at the cells `Allen.ofPosition` of the positions `present`, `past` and
`presentᶜ`. The operator OP_π of
(73) rebinds `π` for a whole clause, so a clausemate tense and ⌜then⌝, which restricts the tense's
reference (76), read the same `π`, and a present clashes with ⌜then⌝ whatever `π` is. A deleted
tense carries no presupposition, (86)–(87).

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
* [anand-toosarvandani-2019]
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

variable {T : Type*} [LinearOrder T] {B : Finset Allen.Relation} {C : Finset Ordering}
  {r th π : NonemptyInterval T}

/-! ### The clash and the shift-together effect (section 5) -/

-- (69)
theorem presup_present : Presup (Allen.ofPosition ⟦present⟧) π r ↔ r.Overlaps π := by
  simp [denote_present]

-- (70)
theorem presup_past : Presup (Allen.ofPosition ⟦past⟧) π r ↔ r.Precedes π := by
  simp [denote_past]

/-- A present-tensed clause modified by a distal adverb is contradictory whatever the perspective
((75), (78), (81)–(82)). -/
theorem not_restricted_present {a : DeicticAdverb} (ha : a.IsDistal) (r th π : NonemptyInterval T) :
    ¬ Restricted (Allen.ofPosition ⟦present⟧) (Allen.ofPosition a.cell) π r th :=
  fun ⟨hr, hle, hth⟩ ↦ not_presup_of_presup_overlaps ha (presup_overlaps.2 (presup_present.1 hr))
    hle hth

/-- Anand and Toosarvandani's present, their (11a), presupposes containment in the perspective,
and a distal adverb is excluded with it all the same. -/
theorem not_restricted_le {a : DeicticAdverb} (ha : a.IsDistal) (r th π : NonemptyInterval T) :
    ¬ Restricted Allen.le (Allen.ofPosition a.cell) π r th :=
  fun ⟨hr, hle, hth⟩ ↦ not_presup_of_presup_overlaps ha
    (presup_overlaps.2 (NonemptyInterval.overlaps_of_le (presup_le.1 hr))) hle hth

/-- The ⌜then⌝ adverbs of the paper's sample, by the Glottocode of their language. -/
def thenAdverbs : List (String × DeicticAdverb) :=
  [("stan1293", English.TemporalDeictic.then_),
    ("mode1248", Greek.StandardModern.TemporalDeictic.tote),
    ("hebr1245", Hebrew.TemporalDeictic.az), ("russ1263", Russian.TemporalDeictic.togda),
    ("nucl1643", Japanese.TemporalDeictic.tooji)]

-- (12)
theorem not_restricted_present_of_mem {a : DeicticAdverb} (ha : a ∈ thenAdverbs.map Prod.snd)
    (r th π : NonemptyInterval T) :
    ¬ Restricted (Allen.ofPosition ⟦present⟧) (Allen.ofPosition a.cell) π r th :=
  not_restricted_present ((by decide : ∀ a ∈ thenAdverbs.map Prod.snd, a.IsDistal) a ha) r th π

-- (115)
theorem restricted_present_sejchas (r : NonemptyInterval T) :
    Restricted (Allen.ofPosition ⟦present⟧)
      (Allen.ofPosition Russian.TemporalDeictic.sejchas.cell) r r r :=
  ⟨presup_present.2 (NonemptyInterval.overlaps_refl r), le_rfl,
    presup_present.2 (NonemptyInterval.overlaps_refl r)⟩

/-- With pronominal anchors, PRES and ⌜then⌝ could take different times and the clause would be
coherent (36). -/
theorem exists_split_anchor {π₁ π₂ : NonemptyInterval T} (h : ¬ π₁.Overlaps π₂) :
    ∃ r th, Presup (Allen.ofPosition ⟦present⟧) π₁ r ∧ r ≤ th ∧
      Presup (Allen.ofPosition ⟦present⟧ᶜ) π₂ th :=
  ⟨π₁, π₁, presup_present.2 (NonemptyInterval.overlaps_refl π₁), le_rfl,
    by simpa [denote_present] using h⟩

/-! ### Past and deleted tense (sections 3 and 6) -/

-- (38), (39), (44)
theorem restricted_past_self (hC : .lt ∈ C) (h : Presup (Allen.ofPosition ⟦past⟧) π r) :
    Restricted (Allen.ofPosition ⟦past⟧) (Allen.ofPosition C) π r r :=
  ⟨h, le_rfl, by rwa [presup_ofPosition, NonemptyInterval.position_eq_lt.2 (presup_past.1 h)]⟩

-- (32)
theorem presup_then_not_tooji_of_precedes (h : π.Precedes th) :
    Presup (Allen.ofPosition English.TemporalDeictic.then_.cell) π th ∧
      ¬ Presup (Allen.ofPosition Japanese.TemporalDeictic.tooji.cell) π th := by
  simp [English.TemporalDeictic.then_, Japanese.TemporalDeictic.tooji, denote_present,
    denote_past, NonemptyInterval.position_eq_gt.2 h]

-- (86), (87)
theorem restricted_top_iff : Restricted ⊤ B π r th ↔ r ≤ th ∧ Presup B π th :=
  and_iff_right presup_top

-- (89a)
theorem restricted_top_of_not_overlaps (h : ¬ r.Overlaps π) :
    Restricted ⊤ (Allen.ofPosition ⟦present⟧ᶜ) π r r :=
  restricted_top_iff.2 ⟨le_rfl, by simpa [denote_present] using h⟩

-- (89b)
theorem not_restricted_top_of_le (hC : .eq ∉ C) (hr : r ≤ π) :
    ¬ Restricted ⊤ (Allen.ofPosition C) π r th :=
  fun ⟨_, hle, hth⟩ ↦ not_presup_of_presup_overlaps hC
    (presup_overlaps.2 (NonemptyInterval.overlaps_of_le hr)) hle hth

/-! ### The examples -/

/-- The positions of the tense an example's adverb restricts: its embedded tense, or else its
matrix tense, and all positions for a deleted tense. -/
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
      (.variable ≤ row.judgment ↔ ∃ π r th : NonemptyInterval T,
        Restricted (Allen.ofPosition C) (Allen.ofPosition a.cell) π r th) := by
  simp only [exists_restricted_ofPosition_iff]
  decide +kernel

/-! ### Perspective-sensitive *now* (section 7) -/

-- (112), (114), (115)
theorem not_restricted_past_of_le (hth : th ≤ π) :
    ¬ Restricted (Allen.ofPosition ⟦past⟧) B π r th :=
  fun ⟨hr, hle, _⟩ ↦ NonemptyInterval.precedes_not_overlaps (presup_past.1 hr)
    (NonemptyInterval.overlaps_of_le (hle.trans hth))

-- (114), (115)
theorem exists_restricted_past_present {a b : T} (hab : a < b) :
    ∃ r th π : NonemptyInterval T,
      Restricted (Allen.ofPosition ⟦past⟧) (Allen.ofPosition ⟦present⟧) π r th :=
  ⟨.pure a, ⟨(a, b), hab.le⟩, .pure b, presup_past.2 (by exact hab),
    NonemptyInterval.le_def.2 ⟨le_rfl, hab.le⟩, presup_present.2 ⟨hab.le, le_rfl⟩⟩

end TsiliaZhao2026
