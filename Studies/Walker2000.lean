module

public import Linglib.Data.Wordlist.Walker2000
public import Linglib.Phonology.Harmony.Nasal
public import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Walker (2000): Nasalization, Neutral Segments, and Opacity Effects

Nasal harmonies differ in the segments that nasality spreads through, and the variation follows
one hierarchy: vowels, glides, liquids, fricatives, obstruent stops. A language is a cut on the
hierarchy, with the classes above the cut undergoing and the classes below it blocking. This
file enters three of the languages of the typology as nasal harmonies in the sense of
`Phonology.Harmony.nasalSpread`. In Sundanese nasality spreads rightward from a nasal stop
through vowels and glottals; in the Johore dialect of Malay, through glides as well; in the
Kolokuma dialect of Ijo it spreads leftward from a nasal consonant or a nasal vowel, through
liquids as well.

The underlying form of a printed form is the form without the nasality that the harmony
supplies. Each harmony derives every printed form of its language from its underlying form, and
no other cut on the hierarchy does.

## Implementation notes

* The printed forms are surface forms. `underlying` removes nasality from a target that stands
  next to a nasal trigger or target on the side nasality comes from, and leaves the rest of the
  form as printed.
* The cut of Sundanese is at the glottals, which the forms show nasalized after a nasal span.
* The segments are those of the PHOIBLE chart for the printed symbols.

## TODO

* The forms of Scottish Gaelic, where fricatives undergo, and of Tuyuca, where no segment
  blocks and voiceless obstruents surface oral inside a nasal span.
* The derivation of the cuts from the ranking of the spreading constraint among the constraints
  against nasalized segments, and the analysis of transparent obstruents by sympathy.
* The survey of the appendix.

## References

* [R. Walker, *Nasalization, Neutral Segments, and Opacity Effects* (2000)][walker-2000]
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

/-- (12): the cut of a language on the nasalization hierarchy, the least compatible class that
undergoes. -/
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
  nasalSpread (IsTrigger l) c (direction l)

/-- The harmony of a language. -/
def harmony (l : Wordlist.Language) : SearchCopy Segment := harmonyAt l (cut l)

/-! ### Underlying forms -/

/-- A form read from the side nasality comes from, without the nasality of a target that follows
a nasal trigger or target. -/
def strip (l : Wordlist.Language) : Option Segment → List Segment → List Segment
  | _, [] => []
  | p, s :: w =>
    (if (cut l).IsTarget s ∧ ∃ a ∈ p, IsNasalSource (IsTrigger l) (cut l) a then
      s.setFeature .nasal false else s) :: strip l (some s) w

/-- The underlying form of a surface form: the form without the nasality that the harmony of
its language supplies. -/
def underlying (l : Wordlist.Language) (w : List Segment) : List Segment :=
  (direction l).orient (strip l none ((direction l).orient w))

/-! ### The forms -/

/-- The segment that a symbol of the transcription writes, a tilde nasalizing it. -/
def ofGlyph? (g : String) : Option Segment :=
  let base : String → Option Segment
    | "a" => some (.ofChart .«a») | "i" => some (.ofChart .«i») | "u" => some (.ofChart .«u»)
    | "o" => some (.ofChart .«o») | "ɔ" => some (.ofChart .«ɔ») | "ə" => some (.ofChart .«ə»)
    | "ɤ" => some (.ofChart .«ɤ») | "j" => some (.ofChart .«j») | "w" => some (.ofChart .«w»)
    | "h" => some (.ofChart .«h») | "ʔ" => some (.ofChart .«ʔ») | "l" => some (.ofChart .«l»)
    | "r" => some (.ofChart .«r») | "ɾ" => some (.ofChart .«ɾ») | "s" => some (.ofChart .«s»)
    | "z" => some (.ofChart .«z») | "p" => some (.ofChart .«p») | "b" => some (.ofChart .«b»)
    | "t" => some (.ofChart .«t») | "d" => some (.ofChart .«d») | "k" => some (.ofChart .«k»)
    | "g" => some (.ofChart .«ɡ») | "gb" => some (.ofChart .«ɡb») | "m" => some (.ofChart .«m»)
    | "n" => some (.ofChart .«n») | "ɲ" => some (.ofChart .«ɲ») | "ŋ" => some (.ofChart .«ŋ»)
    | _ => none
  (base g).or ((base (String.ofList (g.toList.filter (· ≠ '̃')))).map
    (·.setFeature .nasal true))

/-- The printed form of a row. -/
def form? (a : Wordlist.Analysis) : Option (List Segment) := a.form.segments.mapM ofGlyph?

-- (3)–(5): the harmony of each language derives each of its forms from its underlying form
theorem apply_underlying : ∀ a ∈ Wordlist.analyses, ∃ w ∈ form? a,
    (harmony a.language).apply (underlying a.language w) = w := by
  decide +kernel

/-- (12): the cut of a language is the only cut on the hierarchy whose harmony derives every
form of the language from its underlying form. -/
theorem apply_underlying_iff (l : Wordlist.Language) (c : NasalCompatibility) :
    (∀ a ∈ Wordlist.analyses, a.language = l → ∃ w ∈ form? a,
      (harmonyAt l c).apply (underlying l w) = w) ↔ c = cut l := by
  cases l <;> cases c <;> decide +kernel

-- the printed forms are their own surface forms
theorem apply_form : ∀ a ∈ Wordlist.analyses, ∃ w ∈ form? a,
    (harmony a.language).apply w = w := by
  decide +kernel

end Walker2000
