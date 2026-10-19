module

public import Linglib.Semantics.Reference.Animacy
public import Linglib.Semantics.Reference.Nominality
public import Mathlib.Order.Prod.Lex.Basic
public import Linglib.Fragments.Turkish.ObjectMarking
public import Linglib.Syntax.Case.Alignment
public import Linglib.Phonology.OptimalityTheory.Constraint.ForbiddenPairs
public import Linglib.Phonology.OptimalityTheory.Tableau

/-!
# Aissen (2003): Differential Object Marking: Iconicity vs. Economy

The higher in prominence a direct object, the more likely it is to be overtly
case-marked. Aissen derives this in OT: harmonic alignment of the
animacy and definiteness scales with the relational scale, locally conjoined
with \*Ø_C, yields a fixed subhierarchy of iconicity constraints \*Oj/X & \*Ø_C
("penalize a zero-marked object at prominence X"), and a single economy
constraint \*STRUC_C ("penalize overt case morphology") interpolates into it.
The interpolation point is the grammar: an object is obligatorily marked iff
its iconicity constraint outranks \*STRUC_C, so each of the n + 1 points on an
n-level scale is a language type, and every type marks an upward-closed
segment of the scale. The subhierarchies' derivation by harmonic alignment
(the paper's §§2–3) is taken as given; the constraint lists below are written
directly in their derived ranking.

A language's zone, a set of cells of the grid of animacy and definiteness, records *obligatory*
marking — the zone whose constraints strictly dominate \*STRUC_C. The paper's
optional zones (constraints that rerank with \*STRUC_C, stochastically in
Boersma's sense) are noted in docstrings but not represented.

## Main results

- `dom_fits`, `dom_obligatory_zone_upperSet` — the paper's (33b): every attested
  system fits Figure 4's product prominence order (`Alignment.Fits`), its
  obligatory zone an upper set.
- `figure2_typology` / `figure2_languages` — the six interpolation points on
  the definiteness subhierarchy generate exactly the six cutoff systems,
  matched type-for-type to Kalkatungu, Catalan, Pitjantjatjara, Hebrew,
  Turkish, and Written Japanese.
- `figure3_typology` / `figure3_languages` — likewise for the animacy scale.
- `two_dimensional_systems` — Hindi and both stages of Spanish need both
  scales.

## References

* [aissen-2003]
-/

@[expose] public section

namespace Aissen2003

open Reference (Animacy Nominality DefinitenessDegree Definiteness)
open OptimalityTheory

/-! ### The definiteness scale -/

/-- A position on the Definiteness Scale (13), Pronoun > Name > Definite > Indefinite Specific >
NonSpecific, which extends the familiar hierarchy definite > specific > non-specific to proper
names and personal pronouns. -/
inductive DefinitenessScale where
  | nonSpecific
  | indefiniteSpecific
  | definite
  | properName
  | personalPronoun
  deriving DecidableEq, Repr, Fintype

namespace DefinitenessScale

/-- A position is a nominality and a degree of definiteness, pronouns and names counting as the
high end of the definites. -/
def dimensions : DefinitenessScale → Nominality × DefinitenessDegree
  | .personalPronoun => (.pronoun, .definite)
  | .properName => (.properName, .definite)
  | .definite => (.commonNoun, .definite)
  | .indefiniteSpecific => (.commonNoun, .specific)
  | .nonSpecific => (.commonNoun, .nonSpecific)

/-- The scale is ordered by nominality first and then by degree of definiteness. -/
instance : LinearOrder DefinitenessScale := LinearOrder.lift' (toLex ∘ dimensions) (by decide)

/-- The positions, most prominent first. -/
def all : List DefinitenessScale :=
  [.personalPronoun, .properName, .definite, .indefiniteSpecific, .nonSpecific]

/-- The nominality of a position. -/
def nominality (d : DefinitenessScale) : Nominality := d.dimensions.1

/-- The degree of definiteness of a position, pronouns and names being definite. -/
def degree (d : DefinitenessScale) : DefinitenessDegree := d.dimensions.2

/-- The definiteness of a position, definite for pronouns, names and definite NPs. -/
def definiteness (d : DefinitenessScale) : Definiteness := d.degree.definiteness

theorem nominality_monotone : Monotone nominality := by
  intro a b; revert a b; decide

theorem degree_monotone : Monotone degree := by
  intro a b; revert a b; decide

theorem definiteness_monotone : Monotone definiteness := by
  intro a b; revert a b; decide

end DefinitenessScale

/-! ### The DOM systems of the paper

The one-dimensional definiteness systems are the six interpolation types of
Figure 2, one cited language each; Ritharngu and Dhargari instantiate the
clean animacy types of Figure 3 (Yiddish and Sinhalese sit at its
optional-zone points). Hindi, Persian, and the two stages of Spanish are the
two-dimensional systems of §5. -/

section DOMLanguages

/-- Catalan marks only strong personal-pronoun objects, with *a* (Figure 2, §4.1). -/
abbrev catalanDOM : Set (Animacy × DefinitenessScale) := Set.Ici (.inanimate, .personalPronoun)

/-- Pitjantjatjara case-marks only pronoun and proper-name objects (Figure 2). -/
abbrev pitjantjatjaraDOM : Set (Animacy × DefinitenessScale) := Set.Ici (.inanimate, .properName)

/-- Catalan's and Pitjantjatjara's cuts lie in the nominality the scale puts above the
definites: Catalan marks exactly the pronouns, and Pitjantjatjara the pronouns and names. -/
theorem catalan_pitjantjatjara_nominality (a : Animacy) (d : DefinitenessScale) :
    ((a, d) ∈ catalanDOM ↔ d.nominality = .pronoun) ∧
      ((a, d) ∈ pitjantjatjaraDOM ↔ .properName ≤ d.nominality) := by
  revert a d; decide

/-- Hebrew has *ʔet* obligatorily on pronoun, proper-name and definite objects (Figure 2,
§4.1). -/
abbrev hebrewDOM : Set (Animacy × DefinitenessScale) := Set.Ici (.inanimate, .definite)

/-- Hebrew's DOM distinguishes definites from indefinites, marking an object just when it is
definite, pronouns and names included. -/
theorem hebrew_marks_definites (a : Animacy) (d : DefinitenessScale) :
    (a, d) ∈ hebrewDOM ↔ d.definiteness = .definite := by
  revert a d; decide

/-- Turkish marks every object but the non-specific ones, so unlike Hebrew it marks specific
indefinites obligatorily (Figure 2, Tableaux 1–2); the zone is the fragment's, read through the
degree of definiteness. -/
abbrev turkishDOM : Set (Animacy × DefinitenessScale) :=
  {c | c.2.degree ∈ Turkish.ObjectMarking.accusative}

/-- Persian has *-rā* obligatorily on all definites regardless of animacy and, exactly as in
Turkish, on specific indefinites (§5.3). Animacy enters only in the optional zone, the
non-specific indefinites, so the obligatory zone is one-dimensional. -/
abbrev persianDOM : Set (Animacy × DefinitenessScale) := Set.Ici (.inanimate, .indefiniteSpecific)

/-- Written Japanese case-marks all objects, DOM extended to the whole scale, "thereby
ceasing to be differential" (Figures 2–3, fn. 33). -/
abbrev writtenJapaneseDOM : Set (Animacy × DefinitenessScale) := Set.univ

/-- Ritharngu case-marks all human objects obligatorily; the "some animates" spillover the
paper reports is in the optional zone (Figure 3). -/
abbrev ritharnguDOM : Set (Animacy × DefinitenessScale) := Set.Ici (.human, .nonSpecific)

/-- Dhargari case-marks all animate objects (Figure 3). -/
abbrev dhargariDOM : Set (Animacy × DefinitenessScale) := Set.Ici (.animate, .nonSpecific)

/-- The system with no DOM marks no object, Kalkatungu in Figures 2–3, where \*STRUC_C
dominates the whole subhierarchy. -/
abbrev noDOM : Set (Animacy × DefinitenessScale) := ∅

/-- Hindi marks with *-ko* (§5.2, Figure 7). It is obligatory on human objects down to specific
indefinites and on animate pronouns and proper names, which "assimilate to the human class";
optional on human non-specifics, animate definites and below, and inanimate definites; and
excluded on other inanimates. -/
abbrev hindiDOM : Set (Animacy × DefinitenessScale) :=
  Set.Ici (.human, .indefiniteSpecific) ∪ Set.Ici (.animate, .properName)

/-- The Spanish of the Cantar de Mio Cid has *a* obligatorily on exactly the personal pronouns
and proper names of humans and animals (§5.1, Figure 5), and optionally on human common
NPs and geographic proper names. -/
abbrev cmcSpanishDOM : Set (Animacy × DefinitenessScale) := Set.Ici (.animate, .properName)

/-- Modern Spanish is the CMC system with \*STRUC_C demoted below the human-definite and
human-specific constraints, so *a* is now also obligatory with definite and specific human
objects (§5.4, Figure 9). The obligatory zone coincides with Hindi's; the two differ in their
optional zones (Figure 7 against Figure 9). -/
abbrev spanishDOM : Set (Animacy × DefinitenessScale) :=
  Set.Ici (.human, .indefiniteSpecific) ∪ Set.Ici (.animate, .properName)

end DOMLanguages

/-- The DOM systems cited in the paper. -/
def allDOMZones : List (Set (Animacy × DefinitenessScale)) :=
  [catalanDOM, pitjantjatjaraDOM, hebrewDOM, turkishDOM, persianDOM,
   writtenJapaneseDOM, ritharnguDOM, dhargariDOM, hindiDOM, cmcSpanishDOM,
   spanishDOM, noDOM]

/-! ### Monotonicity: the (33b) universal -/

open Alignment

open Classical in
/-- The marking of a DOM system, the object overtly marked on its zone and no other role
marked. -/
noncomputable def marking (z : Set (Animacy × DefinitenessScale)) :
    ArgumentRole → Animacy × DefinitenessScale → Option Unit
  | .P, c => if c ∈ z then some () else none
  | _, _ => none

/-- A DOM system fits the prominence order of Figure 4 exactly when its zone is an upper
set. -/
theorem fits_marking_iff (z : Set (Animacy × DefinitenessScale)) :
    Fits (marking z) ↔ IsUpperSet z := by
  have hA : overt (marking z) .A = ∅ := by ext; simp [marking]
  have hP : overt (marking z) .P = z := by ext; simp [marking]
  simp [Fits, hA, hP, isLowerSet_empty]

/-- In every attested system the obligatorily marked cells form an upper set in the product
prominence order of Figure 4, which is (33b) order-theoretically. -/
theorem dom_obligatory_zone_upperSet : ∀ z ∈ allDOMZones, IsUpperSet z := by
  simp only [allDOMZones, List.mem_cons, List.not_mem_nil, or_false]
  rintro z (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals first
    | exact isUpperSet_Ici _
    | exact isUpperSet_univ
    | exact isUpperSet_empty
    | exact (isUpperSet_Ici _).union (isUpperSet_Ici _)
    | exact (isUpperSet_Ici _).preimage (DefinitenessScale.degree_monotone.comp monotone_snd)

/-- Every attested system fits the prominence order, so no language obligatorily marks a less
prominent object while leaving a more prominent one unmarked. -/
theorem dom_fits : ∀ z ∈ allDOMZones, Fits (marking z) :=
  fun z hz ↦ (fits_marking_iff z).2 (dom_obligatory_zone_upperSet z hz)

/-- On a finite scale the upper sets are the empty set and the cones above each position, so
each of the n + 1 interpolation points of an n-level subhierarchy is a cutoff type. -/
theorem isUpperSet_iff_eq_empty_or_Ici {α : Type*} [LinearOrder α] [WellFoundedLT α]
    {s : Set α} : IsUpperSet s ↔ s = ∅ ∨ ∃ a, s = Set.Ici a :=
  ⟨IsUpperSet.eq_empty_or_Ici, by
    rintro (rfl | ⟨a, rfl⟩)
    exacts [isUpperSet_empty, isUpperSet_Ici a]⟩

/-- A zone depends on animacy alone. -/
def AnimacyOnly (z : Set (Animacy × DefinitenessScale)) : Prop :=
  ∀ a d d', (a, d) ∈ z ↔ (a, d') ∈ z

/-- A zone depends on definiteness alone. -/
def DefinitenessOnly (z : Set (Animacy × DefinitenessScale)) : Prop :=
  ∀ a a' d, (a, d) ∈ z ↔ (a', d) ∈ z

instance (z : Set (Animacy × DefinitenessScale)) [DecidablePred (· ∈ z)] :
    Decidable (AnimacyOnly z) :=
  inferInstanceAs (Decidable (∀ _ _ _, _))

instance (z : Set (Animacy × DefinitenessScale)) [DecidablePred (· ∈ z)] :
    Decidable (DefinitenessOnly z) :=
  inferInstanceAs (Decidable (∀ _ _ _, _))

/-- The Figure 2 and §5.3 systems are animacy-blind. -/
theorem definiteness_systems_one_dimensional :
    DefinitenessOnly catalanDOM ∧ DefinitenessOnly pitjantjatjaraDOM ∧
      DefinitenessOnly hebrewDOM ∧ DefinitenessOnly turkishDOM ∧
      DefinitenessOnly persianDOM ∧ DefinitenessOnly writtenJapaneseDOM := by
  decide

/-- The Figure 3 systems are definiteness-blind. -/
theorem animacy_systems_one_dimensional : AnimacyOnly ritharnguDOM ∧ AnimacyOnly dhargariDOM := by
  decide

/-- Hindi and both stages of Spanish are genuinely two-dimensional (§5), since neither scale
alone determines the obligatory zone. -/
theorem two_dimensional_systems :
    (¬ AnimacyOnly hindiDOM ∧ ¬ DefinitenessOnly hindiDOM) ∧
      (¬ AnimacyOnly cmcSpanishDOM ∧ ¬ DefinitenessOnly cmcSpanishDOM) ∧
      (¬ AnimacyOnly spanishDOM ∧ ¬ DefinitenessOnly spanishDOM) := by
  decide

/-! ### The interpolation engine

The paper evaluates candidates per input: for an object at prominence level
`ℓ`, GEN offers a case-marked and a zero-marked parse. \*Oj/ℓ & \*Ø_C
penalizes the zero-marked parse; \*STRUC_C penalizes the case-marked one. A
grammar linearizes the fixed subhierarchy with \*STRUC_C interpolated, and
the winner at `ℓ` is the marked parse iff `ℓ`'s iconicity constraint
outranks \*STRUC_C. -/

variable {L : Type} [DecidableEq L]

/-- \*STRUC_C penalizes overt case morphology, so the case-marked parse violates it.
Candidates are level–marking pairs, and `true` is the marked parse. -/
def starStruc : Constraint (L × Bool) := Constraint.binary (·.2 = true)

/-- \*Oj/ℓ & \*Ø_C is violated by a zero-marked object at level `ℓ`. -/
def starZero (ℓ : L) : Constraint (L × Bool) :=
  Constraint.binary (fun c ↦ c.1 = ℓ ∧ c.2 = false)

/-- The iconicity subhierarchy of a scale (most prominent level first) with
    \*STRUC_C interpolated at position `k`. -/
def interpolation (levels : List L) (k : Nat) : List (Constraint (L × Bool)) :=
  (levels.map starZero).insertIdx k starStruc

/-- Whether the case-marked parse wins for an object at level `ℓ`. -/
def markedWins (ranking : List (Constraint (L × Bool))) (ℓ : L) : Bool :=
  decide ((Tableau.ofList {(ℓ, true), (ℓ, false)} ranking).optimal
    = {(ℓ, true)})

/-- Tableaux 1–2 evaluate a specific indefinite object. In Hebrew \*STRUC_C outranks
\*Oj/Spec & \*Ø_C and the zero parse wins; in Turkish the ranking is reversed and the marked
parse wins. -/
theorem tableaux_1_2 :
    markedWins (interpolation DefinitenessScale.all 3) .indefiniteSpecific = false ∧
    markedWins (interpolation DefinitenessScale.all 4) .indefiniteSpecific = true := by
  constructor <;> decide

/-- The six interpolation points on the definiteness subhierarchy of Figure 2 generate exactly
the six cutoff systems, and no non-monotone pattern arises. -/
theorem figure2_typology :
    (List.range 6).map
        (fun k ↦ DefinitenessScale.all.map (markedWins (interpolation DefinitenessScale.all k)))
      = [[false, false, false, false, false],
         [true,  false, false, false, false],
         [true,  true,  false, false, false],
         [true,  true,  true,  false, false],
         [true,  true,  true,  true,  false],
         [true,  true,  true,  true,  true]] := by decide

/-- Figure 2 cites "one language for each of the possible DOM types", and each cited
language's obligatory grid is its interpolation type's predicted pattern. -/
theorem figure2_languages :
    (∀ a d, (a, d) ∈ noDOM ↔ markedWins (interpolation DefinitenessScale.all 0) d) ∧
    (∀ a d, (a, d) ∈ catalanDOM ↔ markedWins (interpolation DefinitenessScale.all 1) d) ∧
    (∀ a d, (a, d) ∈ pitjantjatjaraDOM ↔ markedWins (interpolation DefinitenessScale.all 2) d) ∧
    (∀ a d, (a, d) ∈ hebrewDOM ↔ markedWins (interpolation DefinitenessScale.all 3) d) ∧
    (∀ a d, (a, d) ∈ turkishDOM ↔ markedWins (interpolation DefinitenessScale.all 4) d) ∧
    (∀ a d, (a, d) ∈ writtenJapaneseDOM ↔
      markedWins (interpolation DefinitenessScale.all 5) d) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Persian's obligatory grid realizes the same interpolation type as Turkish's, since specific
indefinites "require the suffix -rā, exactly as ... the accusative suffix in Turkish"
(§5.3). -/
theorem persian_same_type_as_turkish :
    ∀ c, c ∈ persianDOM ↔ c ∈ turkishDOM := by decide

/-- The four interpolation points on the animacy subhierarchy of Figure 3 generate exactly the
four cutoff systems. -/
theorem figure3_typology :
    (List.range 4).map
        (fun k ↦ Animacy.all.map (markedWins (interpolation Animacy.all k)))
      = [[false, false, false],
         [true,  false, false],
         [true,  true,  false],
         [true,  true,  true]] := by decide

/-- Figure 3's cleanly cutoff languages match their types, Kalkatungu with none, Ritharngu
with the humans, Dhargari with the animates, and Written Japanese and Dhalandji with all. -/
theorem figure3_languages :
    (∀ a d, (a, d) ∈ noDOM ↔ markedWins (interpolation Animacy.all 0) a) ∧
    (∀ a d, (a, d) ∈ ritharnguDOM ↔ markedWins (interpolation Animacy.all 1) a) ∧
    (∀ a d, (a, d) ∈ dhargariDOM ↔ markedWins (interpolation Animacy.all 2) a) ∧
    (∀ a d, (a, d) ∈ writtenJapaneseDOM ↔ markedWins (interpolation Animacy.all 3) a) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- "This account predicts that the reverse is not found, e.g., languages in which only
inanimates are case-marked", since every interpolation grammar marks an upward-closed
segment of the scale. -/
theorem no_reversed_system :
    ∀ k < 4, ∀ a a' : Animacy, a ≤ a' →
      markedWins (interpolation Animacy.all k) a = true →
      markedWins (interpolation Animacy.all k) a' = true := by decide

end Aissen2003
