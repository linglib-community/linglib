module

/-!
# X-marking

Von Fintel and Iatridou call the morphology a language uses to mark non-live possibilities
X-marking, and its absence O-marking. X-marking is dedicated morphology or borrowed from the past,
the imperfective, the future or the subjunctive, the past being the exclusion feature of Iatridou.

## Main definitions

* `Modality.XMarking.MarkingStrategy`: X-marking and O-marking.
* `Modality.XMarking.XMarkingExponent`: a language's X-marking and the morphology it borrows.

## References

* [von-fintel-iatridou-2023]
* [iatridou-2000]
* [schlenker-2004a]
* [mizuno-2024]
-/

@[expose] public section

namespace Modality.XMarking

/-! ### X-marking / O-marking typology ([von-fintel-iatridou-2023]) -/

/-- The strategies by which a language distinguishes live from non-live possibilities, the
typological labels of [von-fintel-iatridou-2023]. -/
inductive MarkingStrategy where
  /-- X-marking is counterfactual morphology, which expands the domain beyond the live
  possibilities, as in the English Anderson conditional (1a) of [mizuno-2024]. -/
  | xMarking
  /-- O-marking is the absence of X-marking. In the Japanese Anderson conditional (4a) of
  [mizuno-2024] the non-past shifts the time of evaluation back, as the historical present does
  ([schlenker-2004a]). -/
  | oMarking
  deriving DecidableEq, Repr

/-- The complementary marking strategy: O-marking "is generally defined as the absence of
X-marking" ([mizuno-2024], §2), so in a minimal pair the alternative realizes the `other` of the
attested strategy. -/
def MarkingStrategy.other : MarkingStrategy → MarkingStrategy
  | .xMarking => .oMarking
  | .oMarking => .xMarking

@[simp]
theorem MarkingStrategy.other_other : ∀ s : MarkingStrategy, s.other.other = s
  | .xMarking | .oMarking => rfl

/-! ### X-marking exponents ([von-fintel-iatridou-2023] §2, "The form") -/

/-- The morphology realizing X-marking is dedicated or borrowed from the past, imperfective,
future or subjunctive ([von-fintel-iatridou-2023] §2); [mizuno-2024] §4.2 adds the Mandarin
perfective. -/
inductive XMarkingHost where
  /-- Dedicated X-morphology with no other use (Hungarian -nA). -/
  | dedicated
  /-- Fake past ([iatridou-2000]; English, Greek, Romance). -/
  | past
  /-- Fake imperfective (Greek, Romance). -/
  | imperfective
  /-- Future / woll (English would; the Greek and Romance consequent). -/
  | future
  /-- Past subjunctive (German, Icelandic). -/
  | subjunctive
  /-- Perfective ([mizuno-2024], §4.2: Mandarin consequent-final le). -/
  | perfective
  deriving DecidableEq, Repr

/-- A language's X-marking exponent is a citation form with the morphology it borrows, which may
be several pieces, as the Greek past and imperfective are. A fragment records it as `xMarking` in
`Fragments/{Language}/Conditionals.lean`. -/
structure XMarkingExponent where
  /-- The citation form. -/
  form : String
  /-- The morphology the exponent borrows. -/
  components : List XMarkingHost
  deriving DecidableEq, Repr

end Modality.XMarking
