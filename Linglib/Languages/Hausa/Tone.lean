module

public import Linglib.Phonology.Tone.Grammatical
public import Mathlib.Data.Finset.Insert

/-!
# Hausa tone

Hausa has three surface tones: high, unmarked in the orthography (*shā* 'drink'), low, marked by
a grave accent (*dà* 'with, and'), and falling, marked by a circumflex (*tî* 'tea'). A fall is a
high and a low on one syllable, and occurs only on a heavy syllable. There is no rising tone: a
low-high sequence that arises on one syllable, as when a vowel is lost, simplifies to low after a
high in the same word and to high elsewhere, so *gawàyī* 'charcoal' shortens to *gawài* and
*tàusàyī* 'pity' to *tàusái* ([newman-2000]).

The definite article is *-n*, or *-r̃* after a feminine singular noun in *-a*, preceded by a
floating low tone. The low turns a final high into a fall, *bàkā* 'bow' and *bàkân* 'the bow',
and attaches vacuously after a low or a fall, *watà* 'month' and *watàn* 'the month'. A few
morphemes have polar tone, the opposite of an adjacent tone: the stabilizer *nē* / *cē* takes the
opposite of the preceding syllable, the possessive markers *nā* / *tā* the opposite of a
following pronoun, and the weak subject pronouns of the light paradigm the opposite of the
adjacent TAM marker. Tone-integrating suffixes give the whole word their melody, as the class 1
plural *-ōCī*, with a copy of the base-final consonant, makes every tone high: *gyàlè* 'shawl',
*gyalōlī* 'shawls'.

## Main definitions

* `Hausa.syllableTones` — the three surface tones as melodies on one syllable
* `Hausa.simplifyRising`, `Hausa.simplifyRisingWord` — the two rules removing a rise
* `Hausa.dockLow` — the floating low of the definite article on a word's final syllable
* `Hausa.polarOf`, `Hausa.polarAfter` — polar tone, and the polar tone after a syllable
* `Hausa.pluralOCi` — the class 1 plural as a replacive-dominant grammatical tone ([rolle-2018])

## Main results

* `Hausa.simplifyRisingWord_mem` — the rules leave every syllable with a surface tone
* `Hausa.dockLow_mem`, `Hausa.getLast?_dockLow` — the definite article creates no new tone and
  leaves the word ending low
* `Hausa.polarAfter_fall` — a polar tone after a fall is high, as after a low, which follows from
  analysing the fall as a high and a low

## Implementation notes

A syllable's tones are its melody, a list of tonal root nodes, so that the fall is `[H, L]` and a
word is a list of syllable melodies. The polar morphemes and the article are lexical items of
other files; their tone is computed here from their host.

## References

* [newman-2000]
* [rolle-2018]
-/

@[expose] public section

namespace Hausa

open Tone (TRN Tune)

/-! ### Surface tones and the absence of a rise -/

/-- The surface tones of a syllable: high, low, and the fall. -/
def syllableTones : Finset (List TRN) := {[.H], [.L], [.H, .L]}

/-- A low-high sequence on one syllable, given the tone before it in the word, simplifies to low
after a high and to high elsewhere; any other melody is unchanged. -/
def simplifyRising (prev : Option TRN) (σ : List TRN) : List TRN :=
  if σ = [.L, .H] then if prev = some .H then [.L] else [.H] else σ

/-- `simplifyRising` across a word, each syllable seeing the last tone of the one before. -/
def simplifyRisingWord : Option TRN → List (List TRN) → List (List TRN)
  | _, [] => []
  | prev, σ :: w => simplifyRising prev σ :: simplifyRisingWord (simplifyRising prev σ).getLast? w

theorem simplifyRising_mem {prev : Option TRN} {σ : List TRN}
    (h : σ ∈ syllableTones ∨ σ = [.L, .H]) : simplifyRising prev σ ∈ syllableTones := by
  unfold simplifyRising
  split_ifs with h₁ <;> simp_all [syllableTones]

/-- A word whose syllables carry surface tones or a rise surfaces with surface tones only. -/
theorem simplifyRisingWord_mem (prev : Option TRN) (w : List (List TRN))
    (h : ∀ σ ∈ w, σ ∈ syllableTones ∨ σ = [.L, .H]) :
    ∀ σ ∈ simplifyRisingWord prev w, σ ∈ syllableTones := by
  induction w generalizing prev with
  | nil => simp [simplifyRisingWord]
  | cons τ w ih =>
    simp only [simplifyRisingWord, List.mem_cons, forall_eq_or_imp] at h ⊢
    exact ⟨simplifyRising_mem h.1, ih _ h.2⟩

/-- *gawàyī* 'charcoal' loses its last vowel, and the rise after a high becomes low: *gawài*. -/
example : simplifyRisingWord none [[.H], [.L, .H]] = [[.H], [.L]] := by decide

/-- *tàusàyī* 'pity' loses its last vowel, and the rise after a low becomes high: *tàusái*. -/
example : simplifyRisingWord none [[.L], [.L, .H]] = [[.L], [.H]] := by decide

/-- *ɗòyī* 'stench' shortens to one syllable, and the rise with nothing before it becomes high:
*ɗwái*. -/
example : simplifyRisingWord none [[.L, .H]] = [[.H]] := by decide

/-! ### The floating low of the definite article -/

/-- A floating low docked on a syllable: after a final high it makes a fall; after a low it
attaches vacuously. -/
def dockLow (σ : List TRN) : List TRN := if σ.getLast? = some .H then σ ++ [.L] else σ

/-- Docking the low on a surface tone gives a surface tone. -/
theorem dockLow_mem : ∀ σ ∈ syllableTones, dockLow σ ∈ syllableTones := by decide

/-- A syllable with a surface tone ends low once the low has docked. -/
theorem getLast?_dockLow : ∀ σ ∈ syllableTones, (dockLow σ).getLast? = some .L := by decide

/-- The last syllable of *bàkā* 'bow' is high and falls in *bàkân* 'the bow'. -/
example : dockLow [.H] = [.H, .L] := by decide

/-- The last syllable of *watà* 'month' is low and stays low in *watàn* 'the month'. -/
example : dockLow [.L] = [.L] := by decide

/-- The last syllable of *fàsfô* 'passport' falls and still falls in *fàsfôn* 'the passport'. -/
example : dockLow [.H, .L] = [.H, .L] := by decide

/-! ### Polar tone -/

/-- The tone opposite to a tone: low opposite a high, high opposite anything else. -/
def polarOf : TRN → TRN
  | .H => .L
  | _ => .H

theorem polarOf_polarOf : ∀ t ∈ [TRN.H, TRN.L], polarOf (polarOf t) = t := by decide

/-- The polar tone after a syllable, opposite to its last tone. -/
def polarAfter (σ : List TRN) : Option TRN := σ.getLast?.map polarOf

/-- After a fall a polar tone is high, as after a low: *nân nē* 'it's here' with *zōbè nē* 'it's a
ring', against *nan nè* 'it's there'. -/
theorem polarAfter_fall : polarAfter [.H, .L] = polarAfter [.L] := rfl

/-! ### Tone-integrating plurals -/

/-- The class 1 plural *-ōCī*, whose all-high tune replaces the tones of the whole word: a
replacive-dominant grammatical tone accompanying a segmental suffix, [rolle-2018]'s auxiliary
prosodic exponence. -/
def pluralOCi : Tune := ⟨[.H], .left⟩

/-- The plural makes the low tones of *gyàlè* 'shawl' high, *gyalōlī* 'shawls'. -/
example :
    (Tone.overwrite [⟨"gya", .L⟩, ⟨"le", .L⟩] pluralOCi).map (·.tone) = [.H, .H] :=
  rfl

end Hausa
