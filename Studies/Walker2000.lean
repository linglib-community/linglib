module

public import Linglib.Data.Wordlist.Walker2000
public import Linglib.Phonology.Harmony.Nasal
public import Linglib.Phonology.Segmental.PHOIBLE
public import Studies.Benua1997

/-!
# Walker (2000): Nasalization, Neutral Segments, and Opacity Effects

Nasal harmonies differ in the segments that nasality spreads through, and the variation follows
one hierarchy: vowels, glides, liquids, fricatives, obstruent stops. A harmony is a cut on the
hierarchy, with the classes above the cut undergoing and the classes below it blocking. This
file enters three harmonies of the typology in the sense of `Phonology.Harmony.nasalSpread`. In
Sundanese nasality spreads rightward from a nasal stop through vowels and glottals; in the
Johore dialect of Malay, through glides as well; in the Kolokuma dialect of Ijo it spreads
leftward from a nasal consonant or a nasal vowel, through liquids as well.

Each harmony fixes every printed form of its language, and a harmony of the language with
another cut does so exactly when its cut is higher: with a lower cut, some segment that the
forms show oral after a nasal span would be nasalized. The oral input of a form is the form
with nasality on its triggers alone. Each harmony maps the oral input of every printed form to
that form, and no harmony of the language with another cut does: with a higher cut the nasality
of the segments between the two cuts is not supplied.

A glottal inside a nasal span is nasalized: nasality spreads between adjacent segments, so a
segment that it does not pass through stops it. [benua-1997] writes the Sundanese laryngeals oral
inside a nasal span and states the constraint on vowels after a nasal over a word without its
laryngeals. The Sundanese forms entered here satisfy that constraint. No cut on the hierarchy
gives the infixed word *d-um-ɤ̃hɤ̃s* of that study, with its laryngeal oral, from *d-um-ɤhɤs*;
the harmony of Sundanese gives it up to the nasality of the laryngeal.

## Implementation notes

* The printed forms are surface forms, and no input is printed for them. The oral input is one
  of the inputs that a harmony maps to a printed form, the printed form being another; it is
  not the underlying form, which by Lexicon Optimization is the input that the grammar maps
  to the output most faithfully.
* The cut of Sundanese is at the glottals, which the forms show nasalized inside a nasal span,
  as the summary of the survey classes them. The glottal stop is not phonemic in Sundanese or
  in Malay.
* The cut is a property of a harmony. A language may have two harmonies with different cuts,
  and none of the three languages here does.
* In Ijo [l] and [n] are in complementary distribution before a vowel, [n] before the nasal
  vowels; the forms are entered with the [n] printed.
* The segments are those of the PHOIBLE chart for the printed symbols.

## TODO

* The forms of Scottish Gaelic, where fricatives undergo, of Capanahua, where nasality spreads
  leftward through the classes of Malay, and of Tuyuca, where no segment blocks and voiceless
  obstruents surface oral inside a nasal span.
* The derivation of the cuts from the ranking of the spreading constraint among the constraints
  against nasalized segments, and the analysis of transparent obstruents by sympathy.
* The survey of the appendix.

## References

* [R. Walker, *Nasalization, Neutral Segments, and Opacity Effects* (2000)][walker-2000]
* [benua-1997]
-/

@[expose] public section

namespace Walker2000

open Phonology Phonology.Harmony Data.PHOIBLE

/-! ### The harmonies -/

/-- The segments that trigger the harmony of a language: the nasal stops, and in Ijo the nasal
vowels as well. -/
def IsTrigger : Wordlist.Language → Segment → Prop
  | .sundanese | .malay => fun s ↦ NasalCompatibility.ofSegment s = .sonorantStop
  | .ijo => fun s ↦ NasalCompatibility.ofSegment s = .sonorantStop ∨
      NasalCompatibility.ofSegment s = .vowel

instance (l : Wordlist.Language) : DecidablePred (IsTrigger l) := by
  cases l <;> unfold IsTrigger <;> infer_instance

/-- (12), (36): the cut of the harmony of a language on the nasalization hierarchy, the least
compatible class that undergoes. -/
def cut : Wordlist.Language → NasalCompatibility
  | .sundanese => .glottal
  | .malay => .glide
  | .ijo => .liquid

/-- The edge the harmony of a language scans from: the left where nasality spreads rightward,
as in Sundanese and Malay, and the right in Ijo. -/
def direction : Wordlist.Language → Edge
  | .sundanese | .malay => .left
  | .ijo => .right

/-- The harmony of a language with the cut `c`. -/
def harmonyAt (l : Wordlist.Language) (c : NasalCompatibility) : SearchCopy Segment :=
  nasalSpread (IsTrigger l) c.IsTarget (direction l)

/-- The harmony of a language. -/
def harmony (l : Wordlist.Language) : SearchCopy Segment := harmonyAt l (cut l)

/-! ### Oral inputs -/

/-- The oral input of a form: the form with nasality on its triggers alone. -/
def oralInput (l : Wordlist.Language) (w : List Segment) : List Segment :=
  w.map fun s ↦ if IsTrigger l s then s else s.setFeature .nasal false

/-! ### The forms -/

/-- The symbols of the transcription, with the segments they write. -/
def symbols : List (String × Segment) :=
  [("a", .ofChart .«a»), ("i", .ofChart .«i»), ("u", .ofChart .«u»), ("ʊ", .ofChart .«ʊ»),
   ("o", .ofChart .«o»), ("ɔ", .ofChart .«ɔ»), ("ə", .ofChart .«ə»), ("ɤ", .ofChart .«ɤ»),
   ("h", .ofChart .«h»), ("ʔ", .ofChart .«ʔ»), ("j", .ofChart .«j»), ("w", .ofChart .«w»),
   ("l", .ofChart .«l»), ("r", .ofChart .«r»), ("ɾ", .ofChart .«ɾ»), ("s", .ofChart .«s»),
   ("z", .ofChart .«z»), ("p", .ofChart .«p»), ("b", .ofChart .«b»), ("t", .ofChart .«t»),
   ("d", .ofChart .«d»), ("k", .ofChart .«k»), ("g", .ofChart .«ɡ»), ("gb", .ofChart .«ɡb»),
   ("m", .ofChart .«m»), ("n", .ofChart .«n»), ("ɲ", .ofChart .«ɲ»), ("ŋ", .ofChart .«ŋ»)]

/-- The segment that a symbol of the transcription writes, a tilde nasalizing it. -/
def ofGlyph? (g : String) : Option Segment :=
  (symbols.lookup g).or ((symbols.lookup (String.ofList (g.toList.filter (· ≠ '̃')))).map
    (·.setFeature .nasal true))

-- the symbols each harmony spreads through: the vowels and glottals, the glides, the liquids
theorem isTarget_symbols :
    (symbols.filterMap fun (g, s) ↦ if (cut .sundanese).IsTarget s then some g else none) =
        ["a", "i", "u", "ʊ", "o", "ɔ", "ə", "ɤ", "h", "ʔ"] ∧
      (symbols.filterMap fun (g, s) ↦ if (cut .malay).IsTarget s then some g else none) =
        ["a", "i", "u", "ʊ", "o", "ɔ", "ə", "ɤ", "h", "ʔ", "j", "w"] ∧
      (symbols.filterMap fun (g, s) ↦ if (cut .ijo).IsTarget s then some g else none) =
        ["a", "i", "u", "ʊ", "o", "ɔ", "ə", "ɤ", "h", "ʔ", "j", "w", "l", "r", "ɾ"] := by
  decide +kernel

/-- The printed form of a row. -/
def form? (a : Wordlist.Analysis) : Option (List Segment) := a.form.segments.mapM ofGlyph?

-- (3)–(5): the harmony of each language fixes each of its forms
theorem apply_form : ∀ a ∈ Wordlist.analyses, ∃ w ∈ form? a,
    (harmony a.language).apply w = w := by
  decide +kernel

-- a harmony with another cut fixes the forms of a language exactly when its cut is higher
theorem apply_form_iff (l : Wordlist.Language) (c : NasalCompatibility) :
    (∀ a ∈ Wordlist.analyses, a.language = l → ∃ w ∈ form? a, (harmonyAt l c).apply w = w) ↔
      cut l ≤ c := by
  cases l <;> cases c <;> decide +kernel

-- (3)–(5): the harmony of each language maps the oral input of each of its forms to the form
theorem apply_oralInput : ∀ a ∈ Wordlist.analyses, ∃ w ∈ form? a,
    (harmony a.language).apply (oralInput a.language w) = w := by
  decide +kernel

/-- (12), (36): the cut of a language is the only cut on the hierarchy whose harmony maps the
oral input of every form of the language to the form. -/
theorem apply_oralInput_iff (l : Wordlist.Language) (c : NasalCompatibility) :
    (∀ a ∈ Wordlist.analyses, a.language = l → ∃ w ∈ form? a,
      (harmonyAt l c).apply (oralInput l w) = w) ↔ c = cut l := by
  cases l <;> cases c <;> decide +kernel

/-! ### Glottals

Glottals inside a nasal span are nasalized, not skipped (§2.2.3). The forms compared are those
of the tableau (51) of [benua-1997], where the laryngeal of *d-um-ɤ̃hɤ̃s* is oral. -/

-- (3): the Sundanese forms have no oral vowel after a nasal, read without their laryngeals
theorem nvOral_form : ∀ a ∈ Wordlist.analyses, a.language = .sundanese →
    ∃ w ∈ form? a, Benua1997.Sundanese.nvOral w = 0 := by
  decide +kernel

/-- §2.2.3: no cut on the hierarchy derives *d-um-ɤ̃hɤ̃s*, with an oral laryngeal between its
nasal vowels, from *d-um-ɤhɤs*: a harmony whose targets include the glottals nasalizes the
laryngeal, and one whose targets do not stops at it. -/
theorem apply_ne_approach (c : NasalCompatibility) :
    (harmonyAt .sundanese c).apply ((Benua1997.Sundanese.approach .a).string .derivative) ≠
      (Benua1997.Sundanese.approach .c).string .derivative := by
  cases c <;> decide +kernel

-- the harmony of Sundanese derives that word up to the nasality of its laryngeal
theorem filter_apply_approach :
    ((harmony .sundanese).apply ((Benua1997.Sundanese.approach .a).string .derivative)).filter
        (fun x : Segment ↦ Benua1997.Sundanese.IsSupralaryngeal x) =
      ((Benua1997.Sundanese.approach .c).string .derivative).filter
        fun x : Segment ↦ Benua1997.Sundanese.IsSupralaryngeal x := by
  decide +kernel

end Walker2000
