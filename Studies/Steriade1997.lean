module

public import Linglib.Data.Experiments.Steriade1997
public import Linglib.Data.Wordlist.Steriade1997
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
a Lex(P, M) condition requires it to share the properties of the listed allomorphs that bear the
morphosyntactic feature it must encode. With one listed allomorph the two together are identity
to it, which is how single-base derivation appears.

The French liaison form *[vɛ̃n] espoir* takes its consonant from the feminine *vaine* and its
vowel from the masculine *vain*, while *joli*, with no consonant to borrow, keeps its hiatus.
English *remédiable* takes the stress of *remédial* to avoid a lapse, and *parody*, whose
paradigm lists no such stem, keeps the lapse of *párodiable*.

## Main definitions

* `lexP`, `lexPM`: the conditions (7) and (9) over a family of phonological properties.
* `Allomorph`, `listed`: an allomorph's segments, stress and cell, and a lexeme's listed ones.
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
category in its cell, and Lex(P, M) compares the listed allomorphs agreeing with the target in
that feature. A condition is violated once however many properties lack a precedent, as the
tableaux mark it. Lex σ' compares rimes, as footnote 3 states it. \*Lapse σσσ counts the
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

open OptimalityTheory Phonology Data.PHOIBLE Data.Wordlist

/-! ### Lexical conservatism conditions -/

section Conditions

variable {Form π κ : Type*} [DecidableEq π] [DecidableEq κ] (L : Finset Form)
  (P : Form → Finset π) (f : Form → κ) {b t : Form}

/-- Lex(P), the paper's (7), lets the allomorph under evaluation have a property of the family
`P` only if some listed allomorph has it. -/
def lexP : Constraint Form := Constraint.binary fun t ↦ ¬ P t ⊆ L.biUnion P

/-- Lex(P, M), the paper's (9), requires the allomorph under evaluation to have every property
of the family `P` that some listed allomorph agreeing with it in the morphosyntactic feature `f`
has. -/
def lexPM : Constraint Form := Constraint.binary fun t ↦ ¬ (L.filter (f · = f t)).biUnion P ⊆ P t

@[simp] theorem lexP_eq_zero_iff : lexP L P t = 0 ↔ P t ⊆ L.biUnion P := by
  simp [lexP]

@[simp] theorem lexPM_eq_zero_iff : lexPM L P f t = 0 ↔ (L.filter (f · = f t)).biUnion P ⊆ P t := by
  simp [lexPM]

/-- A listed allomorph is its own precedent. -/
theorem lexP_of_mem (h : t ∈ L) : lexP L P t = 0 :=
  (lexP_eq_zero_iff L P).2 (Finset.subset_biUnion_of_mem P h)

theorem lexP_singleton : lexP {b} P t = 0 ↔ P t ⊆ P b := by
  simp

theorem lexPM_singleton (hb : f b = f t) : lexPM {b} P f t = 0 ↔ P b ⊆ P t := by
  simp [Finset.filter_singleton, hb]

/-- With one listed allomorph, agreeing with the target in the feature it must encode, Lex(P) and
Lex(P, M) together are identity to it in the property family, so an impoverished paradigm gives
the appearance of single-base derivation (p. 12). -/
theorem lexP_singleton_and_lexPM_singleton_iff (hb : f b = f t) :
    lexP {b} P t = 0 ∧ lexPM {b} P f t = 0 ↔ P t = P b := by
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

/-! ### Allomorphs -/

/-- The boundary tokens, between words and between morphs. -/
def boundaries : List String := ["_", "+"]

/-- An allomorph is its segments, its stressed syllables counted from zero, and its cell. -/
structure Allomorph where
  /-- The segments. -/
  segments : List Segment
  /-- The stressed syllables. -/
  stressed : Finset ℕ
  /-- The cell. -/
  cell : Wordlist.Cell
  deriving DecidableEq

namespace Allomorph

/-- The allomorph of a form is its segments before the first boundary, with the syllables an
accent marks as stressed, in the form's cell. -/
def ofForm (f : Form Wordlist.Cell) : Allomorph :=
  let w := (f.segments.span (· ∉ boundaries)).1
  ⟨w.map segment, ((w.filter fun x ↦ (segment x).IsVowel).findIdxs (· ∈ accented)).toFinset,
    f.cell⟩

variable (a : Allomorph)

/-- The nuclei of an allomorph, its syllabic segments in order. -/
def nuclei : List Segment := a.segments.filter fun x ↦ x.IsVowel

end Allomorph

/-- The segments after the first boundary of a form, the noun after an adjective or the suffix
after a stem. -/
def following (f : Form Wordlist.Cell) : List Segment :=
  ((f.segments.span (· ∉ boundaries)).2.drop 1).map segment

/-- The listed allomorphs of a lexeme are the forms of its paradigms, which (8) and (13)
print. -/
def listed (x : Lexeme) : Finset Allomorph :=
  (((Wordlist.paradigms.filter (·.lexeme = x)).flatMap (·.forms)).map .ofForm).toFinset

/-! ### French liaison -/

namespace Liaison

/-- The liaison forms the sources record for an adjective, accepted or marked. -/
def liaisonForms (x : Lexeme) : List (Form Wordlist.Cell) :=
  (Wordlist.all ++ Wordlist.marked).filter fun f ↦ f.lexeme = x ∧ f.cell = Wordlist.masc_liaison

/-- The candidates for the liaison form of an adjective are its recorded liaison allomorphs and
its listed allomorphs, all in the masculine liaison cell, as in (8). -/
def candidates (x : Lexeme) : Finset Allomorph :=
  ((liaisonForms x).map Allomorph.ofForm).toFinset ∪
    (listed x).image fun a ↦ { a with cell := Wordlist.masc_liaison }

/-- The final consonant of an allomorph, if it ends in one. -/
def finalConsonant (a : Allomorph) : Finset Segment :=
  (a.segments.getLast?.filter fun s ↦ !decide s.IsVowel).toFinset

/-- Lex C], the paper's (8), requires the final consonant of the allomorph to have a featurally
identical counterpart in some listed allomorph. -/
def lexC (L : Finset Allomorph) : Constraint Allomorph := lexP L finalConsonant

/-- \*Hiatus counts the adjacent vowels of the adjective and the noun after it. -/
def noHiatus (n : List Segment) : Constraint Allomorph :=
  fun a ↦ Hiatus.count (a.segments ++ n)

/-- The accented vowel of an allomorph, its last nucleus. -/
def accentedVowel (a : Allomorph) : Finset Segment := a.nuclei.getLast?.toFinset

/-- Lex 'V-gender, the paper's (10), requires the accented vowel of the allomorph to be that of
each listed allomorph of the same gender. -/
def lexVGender (L : Finset Allomorph) : Constraint Allomorph :=
  lexPM L accentedVowel (·.cell.gender)

/-- The rime of the last syllable, the segments from the last vowel on. -/
def rime : List Segment → List Segment
  | [] => []
  | s :: ss => if ∃ x ∈ ss, x.IsVowel then rime ss else s :: ss

/-- Lex σ' (p. 10) requires the stressed syllable of the allomorph to be identical in its
entirety to that of some listed allomorph. -/
def lexSyllable (L : Finset Allomorph) : Constraint Allomorph := lexP L fun a ↦ {rime a.segments}

/-- The tableau of an adjective's liaison form under a ranking of conditions on its listed
allomorphs. -/
def tableau (x : Lexeme) (cs : Finset Allomorph → List (Constraint Allomorph)) :=
  Tableau.ofList (candidates x) (cs (listed x))

variable (n : List Segment) (L : Finset Allomorph)

/-- Lex C] ≫ \*Hiatus before the noun `n`, the ranking of (8). -/
def hiatusRanking : List (Constraint Allomorph) := [lexC L, noHiatus n]

/-- Lex C] ≫ \*Hiatus ≫ Lex 'V-gender ≫ Lex σ', the ranking of (10). -/
def genderRanking : List (Constraint Allomorph) :=
  [lexC L, noHiatus n, lexVGender L, lexSyllable L]

/-- Lex C] ≫ \*Hiatus ≫ Lex σ' ≫ Lex 'V-gender, the ranking of the speakers who say
*[vɛn] espoir* (p. 10). -/
def syllableRanking : List (Constraint Allomorph) :=
  [lexC L, noHiatus n, lexSyllable L, lexVGender L]

/-- The noun *espoir*, as (3b) transcribes it after *vain*. -/
def espoir : List Segment := following Wordlist.vain_espoir

/-- Under Lex C] ≫ \*Hiatus, the paper's (8), a recorded liaison form wins iff the sources accept
it. Both forms of *vain espoir* win, and *joli enfant* with its hiatus beats *\*jolit enfant*,
whose [t] has no precedent. -/
theorem mem_optimal_iff : ∀ f ∈ Wordlist.all ++ Wordlist.marked, f.cell = Wordlist.masc_liaison →
    (Allomorph.ofForm f ∈ (tableau f.lexeme (hiatusRanking (following f))).optimal ↔
      f ∈ Wordlist.all) := by
  decide +kernel

/-- The citation masculine *[vɛ̃] espoir* loses on \*Hiatus, leaving the two winners of (8b). -/
theorem vain_optimal :
    (tableau Wordlist.Lexemes.vain (hiatusRanking espoir)).optimal =
      {.ofForm Wordlist.vain_espoir, .ofForm Wordlist.vain_espoir_fem} := by
  decide +kernel

/-- In the split-base effect (11), *[vɛ̃n] espoir* takes its consonant from the feminine and its
vowel from the masculine. It satisfies Lex C], \*Hiatus and Lex 'V-gender, and being identical to
no listed allomorph it violates Lex σ'. -/
theorem split_base :
    (genderRanking espoir (listed Wordlist.Lexemes.vain)).map (· (.ofForm Wordlist.vain_espoir)) =
      [0, 0, 0, 1] ∧
    ∀ l ∈ listed Wordlist.Lexemes.vain,
      l.segments ≠ (Allomorph.ofForm Wordlist.vain_espoir).segments := by
  decide +kernel

/-- Speakers ranking Lex 'V-gender above Lex σ' say the split-base *[vɛ̃n] espoir* (10). -/
theorem vain_split :
    (tableau Wordlist.Lexemes.vain (genderRanking espoir)).optimal =
      {.ofForm Wordlist.vain_espoir} := by
  decide +kernel

/-- Speakers ranking Lex σ' above Lex 'V-gender say the feminine *[vɛn] espoir* (p. 10). -/
theorem vain_feminine :
    (tableau Wordlist.Lexemes.vain (syllableRanking espoir)).optimal =
      {.ofForm Wordlist.vain_espoir_fem} := by
  decide +kernel

end Liaison

/-! ### English *-able* -/

namespace Able

/-- The stressed syllables of an allomorph with their nuclei. -/
def stressedNuclei (a : Allomorph) : Finset (Segment × ℕ) :=
  (a.nuclei.zipIdx.filter (·.2 ∈ a.stressed)).toFinset

/-- Lex [±stress], the paper's (15), requires each stressed syllable of the stem to have a
stressed correspondent with the same nuclear vowel in some listed allomorph. -/
def lexStress (L : Finset Allomorph) : Constraint Allomorph := lexP L stressedNuclei

/-- The [±stress] value of each syllable of an allomorph, by position. -/
def stressValues (a : Allomorph) : Finset (ℕ × Bool) :=
  (Finset.range a.nuclei.length).image fun i ↦ (i, decide (i ∈ a.stressed))

/-- Lex([±stress], lexcat), the paper's (17), requires each vowel of the stem to agree in
[±stress] with its correspondent in each listed allomorph of the same lexical category. -/
def lexStressVerb (L : Finset Allomorph) : Constraint Allomorph :=
  lexPM L stressValues (·.cell.category)

/-- The syllables of a string of segments that have an onset, counted from zero. Each syllabic
segment heads a syllable, which has an onset when a nonsyllabic segment precedes it. -/
def onsetful (w : List Segment) : Finset ℕ :=
  (((w.zip (none :: w.map some)).filter fun p ↦ p.1.IsVowel).findIdxs
    fun p ↦ p.2.any fun q ↦ !decide q.IsVowel).toFinset

/-- The suffix *-able*, [əbl̩], after the morph boundary of the printed *remédiable*. -/
def able : List Segment := following Wordlist.remediable

/-- \*Lapse σσσ (p. 15) is violated when the *-able* form has three syllables with onsets in
one stretch of stressless syllables. -/
def noLapse : Constraint Allomorph := Constraint.binary fun a ↦
  ∃ i ∈ onsetful (a.segments ++ able), ∃ k ∈ onsetful (a.segments ++ able),
    Disjoint (Finset.Icc i k) a.stressed ∧
      3 ≤ (onsetful (a.segments ++ able) ∩ Finset.Icc i k).card

/-- The verb of a base. -/
def lexeme : Base → Lexeme
  | .remedy => Wordlist.Lexemes.remedy
  | .parody => Wordlist.Lexemes.parody

/-- The *-able* derivations the sources record on a base. -/
def derivations (b : Base) : List (FormRelation (Form Wordlist.Cell)) :=
  Wordlist.relations.filter (·.form.lexeme = lexeme b)

/-- The verbal stem of the *-able* form of a derivation with a stress pattern of (14). Unchanged
it is the verb, shifted to the second syllable it is the stem of the printed *-able* form, and on
the first and third syllables it is the verb restressed. -/
def candidate (r : FormRelation (Form Wordlist.Cell)) : Pattern → Allomorph
  | .sameAsBase => .ofForm r.form
  | .second => { Allomorph.ofForm r.target with cell := Wordlist.verb }
  | .firstThird => { Allomorph.ofForm r.form with stressed := {0, 2} }

/-- The tableau of a derivation's *-able* form under a ranking of conditions on the verb's listed
allomorphs, its candidates those of (14). -/
def tableau (r : FormRelation (Form Wordlist.Cell))
    (cs : Finset Allomorph → List (Constraint Allomorph)) :=
  Tableau.ofList (Finset.univ.image (candidate r)) (cs (listed r.form.lexeme))

variable (L : Finset Allomorph)

/-- Lex [±stress] ≫ \*Lapse σσσ ≫ Lex([±stress], lexcat), the first ranking of (18). -/
def lapseRanking : List (Constraint Allomorph) := [lexStress L, noLapse, lexStressVerb L]

/-- Lex [±stress] ≫ Lex([±stress], lexcat) ≫ \*Lapse σσσ, the second ranking of (18). -/
def verbRanking : List (Constraint Allomorph) := [lexStress L, lexStressVerb L, noLapse]

/-- The sources record an *-able* form on each base. -/
theorem derivations_ne_nil : ∀ b, derivations b ≠ [] := by
  decide

/-- The stem of the verb lapses before *-able*, and the stem stressed on its second syllable
does not (16). -/
theorem noLapse_candidate : ∀ r ∈ Wordlist.relations,
    noLapse (candidate r .sameAsBase) = 1 ∧ noLapse (candidate r .second) = 0 := by
  decide +kernel

/-- A stem stressed on its third syllable has no stressed precedent there, which is why
*rèmedíable* and *pàrodíable* are dispreferred (p. 16). -/
theorem lexStress_firstThird : ∀ r ∈ Wordlist.relations,
    lexStress (listed r.form.lexeme) (candidate r .firstThird) = 1 := by
  decide +kernel

/-- Under the first ranking of (18) *remédiable* wins (16a), and under the second
*rémediable*. -/
theorem remediable : ∀ r ∈ derivations .remedy,
    (tableau r lapseRanking).optimal = {candidate r .second} ∧
      (tableau r verbRanking).optimal = {candidate r .sameAsBase} := by
  decide +kernel

/-- With no stem stressed on its second syllable listed, *paródiable* violates Lex [±stress],
and *párodiable* wins under either ranking despite its lapse (16b). -/
theorem parodiable : ∀ r ∈ derivations .parody,
    (tableau r lapseRanking).optimal = {candidate r .sameAsBase} ∧
      (tableau r verbRanking).optimal = {candidate r .sameAsBase} := by
  decide +kernel

/-- The winners under the first ranking of (18) are the stress patterns with the most responses
in the survey (14). -/
theorem mem_optimal_iff_most_responses : ∀ b, ∀ r ∈ derivations b, ∀ p,
    candidate r p ∈ (tableau r lapseRanking).optimal ↔
      ∀ q, (responses b q).count ≤ (responses b p).count := by
  decide +kernel

end Able

end Steriade1997
