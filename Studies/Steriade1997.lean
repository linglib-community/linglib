module

public import Linglib.Data.Experiments.Steriade1997
public import Linglib.Data.Forms.Steriade1997
public import Linglib.Data.PHOIBLE.Chart
public import Linglib.Phonology.Hiatus
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Phonology.Segmental.PHOIBLE
public import Mathlib.Data.List.SplitBy

/-!
# Steriade (1997): Lexical Conservatism

A novel form may take its phonology from several listed allomorphs of its morpheme at once, the
split-base effect. Steriade derives it from lexical conservatism. A Lex(P) condition lets the
allomorph under evaluation have a phonological property only if some listed allomorph has it, and
a Lex(P, M) condition requires it to share the properties of the listed allomorphs that bear a
morphosyntactic feature it must encode. With one listed allomorph the two together are identity
to it, which is how single-base derivation appears.

The French liaison form *[vɛ̃n] espoir* takes its consonant from the feminine *vaine* and its
vowel from the masculine *vain*, while *joli*, with no consonant to borrow, keeps its hiatus.
English *remédiable* takes the stress of *remédial* to avoid a lapse, and *parody*, whose
paradigm lists no such stem, keeps the lapse of *párodiable*.

## Main definitions

* `lexP`, `lexPM`: the conditions (7) and (9) over a family of phonological properties.
* `Liaison.lexC`, `Liaison.lexVGender`, `Liaison.lexSyllable`: Lex C], Lex 'V-gender, Lex σ'.
* `Able.lexStress`, `Able.noLapse`, `Able.lexStressVerb`: Lex [±stress], \*Lapse σσσ and
  Lex([±stress], lexcat).

## Main results

* `lexP_singleton_and_lexPM_singleton_iff`: one listed allomorph is a base to be identical to.
* `Liaison.mem_optimal_iff`: Lex C] ≫ \*Hiatus selects the liaison forms the sources accept (8).
* `Liaison.vain_split`, `Liaison.vain_feminine`: the two rankings of Lex 'V-gender and Lex σ'.
* `Able.remediable`, `Able.parodiable`: the tableaux (16) under both rankings of (18).
* `Able.mem_optimal_iff_most_responses`: the winners of (18) are the majority responses of (14).

## Implementation notes

A listed allomorph is a form of the paradigm that (8) or (13) prints, its gender or lexical
category in its cell. A condition is violated once however many properties lack a precedent, as
the tableaux mark it. Lex σ' compares rimes, as footnote 3 states it. \*Lapse σσσ counts the
syllables with onsets in a stretch of stressless syllables, the reading on which *rémediable*
violates it in (16a). The stems that (14) prints only in spelling have the segments of the verb.

## TODO

* (14) gives *rémediable* 3 of 24 responses, where (23) prints 20/4 for *remédiable*.
* (19) marks *descríptable* as violating Lex([±stress], lexcat), though its stress matches that
  of *descríbe*.
* Lex (C], lexcat) (27), Lex σ' (28) and the tableau (29) need the coda of the English stressed
  syllable.
* The heterogeneous paradigms of (23), printed in spelling only, and the loose correspondence of
  footnote 3, which rules out *\*[nuvol] an*.

## References

* [steriade-1997]
* [mccarthy-prince-1995]
* [prince-1983]
-/

@[expose] public section

namespace Steriade1997

open OptimalityTheory Phonology Data.PHOIBLE Data.Forms

/-! ### Lexical conservatism conditions -/

section Conditions

variable {Form π : Type*} [DecidableEq π] (L : List Form) (P : Form → Finset π)
  (M : Form → Prop) [DecidablePred M] {b t : Form}

/-- Lex(P), the paper's (7), lets the allomorph under evaluation have a property of the family
`P` only if some listed allomorph has it. -/
def lexP : Constraint Form := Constraint.binary fun t ↦ ¬ ∀ p ∈ P t, ∃ l ∈ L, p ∈ P l

/-- Lex(P, M), the paper's (9), requires the allomorph under evaluation to have every property
of the family `P` that a listed allomorph with the morphosyntactic feature `M` has. -/
def lexPM : Constraint Form := Constraint.binary fun t ↦ ¬ ∀ l ∈ L, M l → P l ⊆ P t

theorem lexP_eq_zero_iff : lexP L P t = 0 ↔ ∀ p ∈ P t, ∃ l ∈ L, p ∈ P l := by
  simp [lexP]

theorem lexPM_eq_zero_iff : lexPM L P M t = 0 ↔ ∀ l ∈ L, M l → P l ⊆ P t := by
  simp [lexPM]

/-- A listed allomorph is its own precedent. -/
theorem lexP_of_mem (h : t ∈ L) : lexP L P t = 0 :=
  (lexP_eq_zero_iff L P).2 fun _ hp ↦ ⟨t, h, hp⟩

theorem lexP_singleton : lexP [b] P t = 0 ↔ P t ⊆ P b := by
  simp [lexP_eq_zero_iff, Finset.subset_iff]

theorem lexPM_singleton (hb : M b) : lexPM [b] P M t = 0 ↔ P b ⊆ P t := by
  simp [lexPM_eq_zero_iff, hb]

/-- With one listed allomorph, bearing the feature the target must encode, Lex(P) and Lex(P, M)
together are identity to it in the property family, so an impoverished paradigm gives the
appearance of single-base derivation (p. 12). -/
theorem lexP_singleton_and_lexPM_singleton_iff (hb : M b) :
    lexP [b] P t = 0 ∧ lexPM [b] P M t = 0 ↔ P t = P b := by
  rw [lexP_singleton, lexPM_singleton _ _ hb, Finset.Subset.antisymm_iff]

end Conditions

/-! ### Segments -/

/-- The segment of a printed token is PHOIBLE's chart entry for its glyph, without its accent.
The English [r] is the approximant ɹ. -/
def segment : String → Segment
  | "v" => FeatureMatrix.«v».toSegment | "ɛ̃" => FeatureMatrix.«ɛ̃».toSegment
  | "ɛ" => FeatureMatrix.«ɛ».toSegment | "n" => FeatureMatrix.«n».toSegment
  | "s" => FeatureMatrix.«s».toSegment | "p" => FeatureMatrix.«p».toSegment
  | "w" => FeatureMatrix.«w».toSegment | "a" => FeatureMatrix.«a».toSegment
  | "ʁ" => FeatureMatrix.«ʁ».toSegment | "ʒ" => FeatureMatrix.«ʒ».toSegment
  | "o" => FeatureMatrix.«o».toSegment | "l" => FeatureMatrix.«l».toSegment
  | "i" => FeatureMatrix.«i».toSegment | "ɑ̃" => FeatureMatrix.«ɑ̃».toSegment
  | "f" => FeatureMatrix.«f».toSegment | "t" => FeatureMatrix.«t».toSegment
  | "r" => FeatureMatrix.«ɹ».toSegment | "ɛ́" => FeatureMatrix.«ɛ».toSegment
  | "m" => FeatureMatrix.«m».toSegment | "ə" => FeatureMatrix.«ə».toSegment
  | "ɾ" => FeatureMatrix.«ɾ».toSegment | "í" => FeatureMatrix.«i».toSegment
  | "d" => FeatureMatrix.«d».toSegment | "ǽ" => FeatureMatrix.«æ».toSegment
  | "ó" => FeatureMatrix.«o».toSegment | "b" => FeatureMatrix.«b».toSegment
  | "l̩" => FeatureMatrix.«l̩».toSegment
  | _ => ⊥

/-- The tokens an accent marks as stressed. -/
def accented : List String := ["ɛ́", "í", "ǽ", "ó"]

/-! ### French liaison -/

namespace Liaison

/-- A French adjective allomorph, its segments and its cell. -/
structure Adjective where
  /-- The segments. -/
  segments : List Segment
  /-- The cell. -/
  cell : Forms.Cell
  deriving DecidableEq

/-- The adjective of a form, its segments before the word boundary, in the form's cell. -/
def Adjective.ofForm (f : Form Forms.Cell) : Adjective :=
  ⟨(f.segments.takeWhile (· ≠ "_")).map segment, f.cell⟩

/-- The noun after the adjective of a phrase, its segments after the word boundary. -/
def noun (f : Form Forms.Cell) : List Segment :=
  ((f.segments.dropWhile (· ≠ "_")).drop 1).map segment

/-- The listed allomorphs of an adjective, the citation forms of its paradigm. -/
def listed (x : Paradigm Forms.Cell) : List Adjective := x.forms.map .ofForm

/-- The liaison forms the sources record for an adjective, accepted or marked. -/
def liaisonForms (x : Lexeme) : List (Form Forms.Cell) :=
  (Forms.all ++ Forms.marked).filter fun f ↦ f.lexeme = x ∧ f.cell = Forms.masc_liaison

/-- The candidates for the liaison form of an adjective are its recorded liaison allomorphs and
its listed allomorphs, all in the masculine liaison cell, as in (8). -/
def candidates (x : Paradigm Forms.Cell) : Finset Adjective :=
  ((liaisonForms x.lexeme).map Adjective.ofForm ++
    (listed x).map fun a : Adjective ↦ { a with cell := Forms.masc_liaison }).toFinset

/-- The final consonant of an allomorph, if it ends in one. -/
def finalConsonant (a : Adjective) : Finset Segment :=
  (a.segments.getLast?.filter fun s ↦ !decide s.IsVowel).toFinset

/-- Lex C], the paper's (8), requires the final consonant of the allomorph to have a featurally
identical counterpart in some listed allomorph. -/
def lexC (L : List Adjective) : Constraint Adjective := lexP L finalConsonant

/-- \*Hiatus counts the adjacent vowels of the adjective and the noun after it. -/
def noHiatus (n : List Segment) : Constraint Adjective :=
  fun a ↦ Hiatus.count (a.segments ++ n)

/-- The accented vowel of an allomorph, its last vowel. -/
def accentedVowel (a : Adjective) : Finset Segment :=
  (a.segments.filter fun s ↦ decide s.IsVowel).getLast?.toFinset

/-- Lex 'V-gender, the paper's (10), requires the accented vowel of the allomorph to be that of
each listed allomorph of its gender, masculine. -/
def lexVGender (L : List Adjective) : Constraint Adjective :=
  lexPM L accentedVowel (·.cell.gender = ↑UD.Gender.Masc)

/-- The rime of the last syllable, the segments from the last vowel on. -/
def rime : List Segment → List Segment
  | [] => []
  | s :: ss => if ∃ x ∈ ss, x.IsVowel then rime ss else s :: ss

/-- Lex σ' (p. 10) requires the stressed syllable of the allomorph to be identical in its
entirety to that of some listed allomorph. -/
def lexSyllable (L : List Adjective) : Constraint Adjective := lexP L fun a ↦ {rime a.segments}

/-- The tableau (8) of an adjective's liaison form before a noun ranks Lex C] above
\*Hiatus. -/
def tableau (x : Paradigm Forms.Cell) (n : List Segment) :=
  Tableau.ofList (candidates x) [lexC (listed x), noHiatus n]

/-- Under Lex C] ≫ \*Hiatus, the paper's (8), a recorded liaison form wins iff the sources accept
it. Both forms of *vain espoir* win, and *joli enfant* with its hiatus beats *\*jolit enfant*,
whose [t] has no precedent. -/
theorem mem_optimal_iff :
    ∀ x ∈ [Forms.vain_listed.paradigm, Forms.joli_listed.paradigm], ∀ f ∈ liaisonForms x.lexeme,
      Adjective.ofForm f ∈ (tableau x (noun f)).optimal ↔ f ∈ Forms.all := by
  decide +kernel

/-- The citation masculine *[vɛ̃] espoir* loses on \*Hiatus, leaving the two winners of (8b). -/
theorem vain_optimal :
    (tableau Forms.vain_listed.paradigm (noun Forms.vain_espoir)).optimal =
      {.ofForm Forms.vain_espoir, .ofForm Forms.vain_espoir_fem} := by
  decide +kernel

/-- In the split-base effect (11), *[vɛ̃n] espoir* takes its consonant from the feminine and its
vowel from the masculine. It satisfies Lex C], \*Hiatus and Lex 'V-gender, and being identical to
no listed allomorph it violates Lex σ'. -/
theorem split_base :
    let L := listed Forms.vain_listed.paradigm
    let s := Adjective.ofForm Forms.vain_espoir
    lexC L s = 0 ∧ noHiatus (noun Forms.vain_espoir) s = 0 ∧ lexVGender L s = 0 ∧
      lexSyllable L s = 1 ∧ ∀ l ∈ L, l.segments ≠ s.segments := by
  decide +kernel

/-- Speakers ranking Lex 'V-gender above Lex σ' say the split-base *[vɛ̃n] espoir* (10). -/
theorem vain_split :
    let L := listed Forms.vain_listed.paradigm
    (Tableau.ofList (candidates Forms.vain_listed.paradigm)
      [lexC L, noHiatus (noun Forms.vain_espoir), lexVGender L, lexSyllable L]).optimal =
        {.ofForm Forms.vain_espoir} := by
  decide +kernel

/-- Speakers ranking Lex σ' above Lex 'V-gender say the feminine *[vɛn] espoir* (p. 10). -/
theorem vain_feminine :
    let L := listed Forms.vain_listed.paradigm
    (Tableau.ofList (candidates Forms.vain_listed.paradigm)
      [lexC L, noHiatus (noun Forms.vain_espoir), lexSyllable L, lexVGender L]).optimal =
        {.ofForm Forms.vain_espoir_fem} := by
  decide +kernel

end Liaison

/-! ### English *-able* -/

namespace Able

/-- An English stem allomorph is its segments, its stressed syllables counted from zero, and
its cell. -/
structure Stem where
  /-- The segments. -/
  segments : List Segment
  /-- The stressed syllables. -/
  stressed : Finset ℕ
  /-- The cell. -/
  cell : Forms.Cell
  deriving DecidableEq

/-- The nuclei of a string of segments, its syllabic segments. -/
def nuclei (w : List String) : List String := w.filter fun x ↦ decide (segment x).IsVowel

/-- The stem of a form, its segments before the morph boundary, with the syllables an accent
marks as stressed. -/
def Stem.ofForm (f : Form Forms.Cell) : Stem :=
  let w := f.segments.takeWhile (· ≠ "+")
  ⟨w.map segment, (((nuclei w).zipIdx.filter (·.1 ∈ accented)).map (·.2)).toFinset, f.cell⟩

/-- The nuclear vowels of a stem's stressed syllables, by position. -/
def stressedNuclei (s : Stem) : Finset (ℕ × Option Segment) :=
  s.stressed.image fun i ↦ (i, (s.segments.filter fun x ↦ decide x.IsVowel)[i]?)

/-- Lex [±stress], the paper's (15), requires each stressed syllable of the stem to have a
stressed correspondent with the same nuclear vowel in some listed allomorph. -/
def lexStress (L : List Stem) : Constraint Stem := lexP L stressedNuclei

/-- The [±stress] value of each syllable of a stem, by position. -/
def stressValues (s : Stem) : Finset (ℕ × Bool) :=
  (Finset.range (s.segments.countP fun x ↦ decide x.IsVowel)).image
    fun i ↦ (i, decide (i ∈ s.stressed))

/-- Lex([±stress], lexcat), the paper's (17), requires each vowel of the stem to agree in
[±stress] with its correspondent in each listed verbal allomorph. -/
def lexStressVerb (L : List Stem) : Constraint Stem :=
  lexPM L stressValues (·.cell.category = ↑Forms.Category.verb)

/-- The suffix *-able*, [əbl̩], after the morph boundary of the printed *remédiable*. -/
def able : List Segment := ((Forms.remediable.segments.dropWhile (· ≠ "+")).drop 1).map segment

/-- `onsets p w` records whether each syllable of `w` has an onset, `p` being the segment before
`w`. Each syllabic segment heads a syllable, with an onset when a nonsyllabic segment precedes
it. -/
def onsets : Option Segment → List Segment → List Bool
  | _, [] => []
  | p, x :: xs =>
    if x.IsVowel then (p.any fun q ↦ !decide q.IsVowel) :: onsets (some x) xs
    else onsets (some x) xs

/-- The syllables of a stem's *-able* form, each as whether it is stressed and whether it has an
onset. The suffix is stressless. -/
def ableSyllables (s : Stem) : List (Bool × Bool) :=
  (onsets none (s.segments ++ able)).zipIdx.map fun p ↦ (decide (p.2 ∈ s.stressed), p.1)

/-- \*Lapse σσσ (p. 15) is violated when the *-able* form has three syllables with onsets in
one stretch of stressless syllables. -/
def noLapse : Constraint Stem := Constraint.binary fun s ↦
  ∃ r ∈ (ableSyllables s).splitBy (fun x y : Bool × Bool ↦ !x.1 && !y.1),
    3 ≤ r.countP fun x ↦ !x.1 && x.2

/-- The verb of a base. -/
def verb : Base → Form Forms.Cell
  | .remedy => Forms.remedy
  | .parody => Forms.parody

/-- The listed allomorphs of a base's paradigm, (13). -/
def listed : Base → List Stem
  | .remedy => Forms.remedy_listed.paradigm.forms.map .ofForm
  | .parody => Forms.parody_listed.paradigm.forms.map .ofForm

/-- The *-able* form of a base stressed on the second syllable, as (14) prints it. -/
def ableForm : Base → Form Forms.Cell
  | .remedy => Forms.remediable
  | .parody => Forms.parodiable

/-- The verbal stem of the *-able* form with a stress pattern of (14). Unchanged it is the verb,
shifted to the second syllable it is the stem of the printed *-able* form, and on the first and
third syllables it is the verb restressed. -/
def candidate (b : Base) : Pattern → Stem
  | .sameAsBase => .ofForm (verb b)
  | .second => { Stem.ofForm (ableForm b) with cell := Forms.verb }
  | .firstThird => { Stem.ofForm (verb b) with stressed := {0, 2} }

/-- The tableau of a base's *-able* form under a ranking, its candidates those of (14). -/
def tableau (b : Base) (cs : List (Constraint Stem)) :=
  Tableau.ofList (Finset.univ.image (candidate b)) cs

/-- Lex [±stress] ≫ \*Lapse σσσ ≫ Lex([±stress], lexcat), the first ranking of (18). -/
def lapseRanking (b : Base) : List (Constraint Stem) :=
  [lexStress (listed b), noLapse, lexStressVerb (listed b)]

/-- Lex [±stress] ≫ Lex([±stress], lexcat) ≫ \*Lapse σσσ, the second ranking of (18). -/
def verbRanking (b : Base) : List (Constraint Stem) :=
  [lexStress (listed b), lexStressVerb (listed b), noLapse]

/-- The stem of the verb lapses before *-able*, and the stem stressed on its second syllable
does not (16). -/
theorem noLapse_candidate :
    ∀ b, noLapse (candidate b .sameAsBase) = 1 ∧ noLapse (candidate b .second) = 0 := by
  decide +kernel

/-- A stem stressed on its third syllable has no stressed precedent there, which is why
*rèmedíable* and *pàrodíable* are dispreferred (p. 16). -/
theorem lexStress_firstThird : ∀ b, lexStress (listed b) (candidate b .firstThird) = 1 := by
  decide +kernel

/-- Under the first ranking of (18) *remédiable* wins (16a), and under the second
*rémediable*. -/
theorem remediable :
    (tableau .remedy (lapseRanking .remedy)).optimal = {candidate .remedy .second} ∧
      (tableau .remedy (verbRanking .remedy)).optimal = {candidate .remedy .sameAsBase} := by
  decide +kernel

/-- With no stem stressed on its second syllable listed, *paródiable* violates Lex [±stress],
and *párodiable* wins under either ranking despite its lapse (16b). -/
theorem parodiable :
    (tableau .parody (lapseRanking .parody)).optimal = {candidate .parody .sameAsBase} ∧
      (tableau .parody (verbRanking .parody)).optimal = {candidate .parody .sameAsBase} := by
  decide +kernel

/-- The winners under the first ranking of (18) are the stress patterns with the most responses
in the survey (14). -/
theorem mem_optimal_iff_most_responses :
    ∀ b p, candidate b p ∈ (tableau b (lapseRanking b)).optimal ↔
      ∀ q, (responses b q).count ≤ (responses b p).count := by
  decide +kernel

end Able

end Steriade1997
