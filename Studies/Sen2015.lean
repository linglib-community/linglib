module

public import Linglib.Phonology.Segmental.Basic
public import Linglib.Fragments.Latin.Phonology
public import Mathlib.Order.Basic

/-!
# Sen (2015): Syllable and Segment in Latin

This file formalizes the second chapter's analysis of clear and dark /l/. The colouring of a
preceding vowel, read off the grammarians' statements and the internal history of Latin words
(§2.3), orders the contexts of /l/ by darkness (18): the syllable coda, then onset /l/ before
/a o u/, before /e/, before /ē/, and last onset /l/ before /i/ and geminate /ll/ (`Context`,
`darkness`; Figure 2.1, `colouring`). The distribution is categorical across three positions and
gradient within one: coda /l/ is dark, geminate /ll/ is clear, and onset /l/ darkens with the
backness of the following vowel. The equipollent analysis (23) states this as surface
specifications on the Fragment's single /l/, `[+high, +back]` in the coda, `[+high, −back]` in
the geminate and `[+high, Ø back]` in the onset (`spec`, `spec_ternary`). The specified variants
sit at the ends of the scale (`coda_darkest`, `geminate_clearest`), colouring follows the scale
(`colouring_monotone`), and the unspecified onset ranges over three degrees (`onset_gradient`):
the specification does not determine darkness, which is why the chapter rejects synchronic
feature spreading as the source of the colouring (§2.5) in favour of phonetic interpolation
through the underspecified segment, in the sense of [keating-1988].

## Implementation notes

* Sen takes /l/ to be underlyingly unspecified for [back], the coda and geminate values being
  filled once a string is syllabified (§2.4); `spec` is the surface specification by position,
  built from the Fragment's /l/ with `Segment.setFeature`.
* `colouring` is the regular outcome of Figure 2.1; its exceptions (after /w j/, after dorsals,
  forms with particular histories) are not encoded. The gradient phonetic implementation
  (Figure 2.3), the diachronic account of the split, and the parallel analysis of /r/ in the
  fourth chapter are out of scope.

## References

* [sen-2015]
* [keating-1988]
-/

@[expose] public section

namespace Sen2015

open Phonology Latin

/-- The three categorical positions of /l/ (19) are the syllable coda, the onset, and the
geminate. -/
inductive Position
  | coda | onset | geminate
  deriving DecidableEq, Repr

/-- The contexts of /l/ that the colouring evidence distinguishes (18), Figure 2.1, are the
coda, onset /l/ before /a o u/, before /e/, before /ē/, before /i/, and the geminate. -/
inductive Context
  | coda | preBack | preE | preLongE | preI | geminate
  deriving DecidableEq, Repr, Fintype

/-- The categorical position of a context. -/
def Context.position : Context → Position
  | .coda => .coda
  | .geminate => .geminate
  | .preBack | .preE | .preLongE | .preI => .onset

/-- The scale of darkness (18), as a rank with the coda highest; onset /l/ before /i/ and the
geminate share the clearest degree. -/
def Context.darkness : Context → ℕ
  | .coda => 4
  | .preBack => 3
  | .preE => 2
  | .preLongE => 1
  | .preI | .geminate => 0

/-- Contexts are ordered by darkness. -/
instance : Preorder Context := Preorder.lift Context.darkness

instance : DecidableRel (α := Context) (· ≤ ·) :=
  fun a b ↦ inferInstanceAs (Decidable (a.darkness ≤ b.darkness))

instance : DecidableRel (α := Context) (· < ·) :=
  fun a b ↦ inferInstanceAs (Decidable (a.darkness < b.darkness))

/-- A short vowel before /l/ is coloured to /u/, coloured to /o/, or left unchanged. -/
inductive Colouring
  | toU | toO | unchanged
  deriving DecidableEq, Repr

/-- The vowel a colouring produces, from the Fragment. -/
def Colouring.vowel : Colouring → Option Segment
  | .toU => some u
  | .toO => some o
  | .unchanged => none

/-- Colouring to /u/ is stronger than colouring to /o/, which is stronger than none. -/
def Colouring.strength : Colouring → ℕ
  | .toU => 2
  | .toO => 1
  | .unchanged => 0

/-- Whether the coloured vowel sits in an internal or an initial syllable (Figure 2.1). -/
inductive Syllable
  | internal | initial
  deriving DecidableEq, Repr

/-- The regular colouring of a preceding short vowel by context (Figure 2.1) is in an internal
syllable to /u/ before the coda and before onset /l/ followed by /a o u/ or /e/, to /o/ before
/lē/, and none before /li/ and /ll/; in an initial syllable to /u/ before the coda and to /o/
before /la lo lu/ only. -/
def colouring : Syllable → Context → Colouring
  | .internal, .coda | .internal, .preBack | .internal, .preE => .toU
  | .internal, .preLongE => .toO
  | .internal, .preI | .internal, .geminate => .unchanged
  | .initial, .coda => .toU
  | .initial, .preBack => .toO
  | .initial, .preE | .initial, .preLongE | .initial, .preI | .initial, .geminate => .unchanged

/-- Colouring follows the scale of darkness (18), in that a darker context colours at least as
strongly in either syllable. -/
theorem colouring_monotone (s : Syllable) : Monotone fun c ↦ (colouring s c).strength := by
  cases s <;> intro c₁ c₂ <;> revert c₁ c₂ <;> decide

/-- The coda is the darkest context and the geminate the clearest ((18), Figure 2.2). -/
theorem coda_darkest (c : Context) : c ≤ .coda := by revert c; decide

theorem geminate_clearest (c : Context) : Context.geminate ≤ c := by revert c; decide

/-- The surface specification of /l/ by position (23) is the Fragment's /l/ with the dorsal
articulation `[+high]` common to the three variants, `[+back]` in the coda, `[−back]` in the
geminate, and no value for `[back]` in the onset. -/
def spec : Position → Segment
  | .coda => (l.setFeature .high true).setFeature .back true
  | .geminate => (l.setFeature .high true).setFeature .back false
  | .onset => l.setFeature .high true

/-- The surface contrast (19), (23) is ternary, with plus, minus and unspecified `[back]`, all
`[+high]`. -/
theorem spec_ternary :
    (spec .coda).HasValue .back true ∧ (spec .geminate).HasValue .back false ∧
      (spec .onset).Unspecified .back ∧ ∀ p, (spec p).HasValue .high true := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro p
  cases p <;> decide

theorem extremes_specified (c : Context) :
    (Context.coda ≤ c → c = .coda) ∧
      (c ≤ .geminate → c = .geminate ∨ c = .preI) := by
  revert c; decide

/-- Within the onset the specification is one and the darkness is not. Before /a o u/, /e/ and
/i/ the same `[Ø back]` /l/ ranges over three degrees, so the categorical specification does not
determine the colouring, the chapter's reason for rejecting synchronic feature spreading as its
mechanism (§2.5). -/
theorem onset_gradient :
    Context.preBack.position = .onset ∧ Context.preE.position = .onset ∧
      Context.preI.position = .onset ∧
      Context.preI < .preE ∧ Context.preE < .preBack := by
  decide

end Sen2015
