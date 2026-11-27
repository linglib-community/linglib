/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Data.Fintype.Prod

/-!
# Segments and features

This file defines the distinctive features and the segments built over them. The features are
the twenty-six of Hayes's charts and the tongue-root features [ATR] and [RTR]. Hayes names
[ATR] but leaves it off his charts, noting that it is unclear whether it is the same feature as
[tense]; it is a feature of its own here. [long] and [stress], which Hayes also names, are not
features here: length is a segment on two timing slots, and stress belongs to syllables. A
segment `s` gives each feature the value `+`, `−` or none (`s f = true`, `s f = false`,
`s f = none`), as a row of a feature chart does.

The file also names some natural classes by their features. The sonority hierarchy is in
`Phonology/Segmental/Sonority/Basic.lean`, and the theorems about segments in
`Phonology/Segmental/Basic.lean`.

## Implementation notes

[syllabic] is a feature of segments here, as in Hayes, for whom a segment is [+syllabic] when it
is the nucleus of its syllable. Elsewhere syllabicity is structure and no segment is specified for
it, so what is a change of position there is a change of feature here, as in glide formation.

## References

* [hayes-2009]: the features of ch. 4 and Table 4.7, the tongue-root feature (p. 83), and the
  manner classes (p. 77)
* [kaisse-2011]: [syllabic] as the head or nucleus of the syllable
* [halle-vaux-wolfe-2000]: [ATR] and [RTR]
-/

@[expose] public section

namespace Phonology

/-! ### Features -/

/-- A distinctive feature. -/
inductive Feature where
  /-- [+syllabic] segments are syllable nuclei. -/
  | syllabic
  /-- [+consonantal] segments are the liquids, nasals and obstruents. -/
  | consonantal
  /-- [−sonorant] segments, the stops, fricatives and affricates, build up air pressure in the
  vocal tract. -/
  | sonorant
  /-- [+approximant] segments are the liquids, glides and vowels. -/
  | approximant
  /-- [−continuant] segments, the stops, affricates and nasals, close the oral tract fully. -/
  | continuant
  /-- [+delayed release] segments, the affricates and fricatives, have frication noise. -/
  | delayedRelease
  /-- [+nasal] segments are the nasal consonants and the nasalized vowels. -/
  | nasal
  /-- [+lateral] segments let air pass around the side of the tongue. -/
  | lateral
  /-- [+strident] segments are the sibilants, coronal fricatives and affricates whose airstream
  is channelled through a groove in the tongue blade. -/
  | strident
  /-- [+tap] distinguishes taps from the other rhotics. -/
  | tap
  /-- [+trill] distinguishes trills from the other rhotics. -/
  | trill
  /-- [+voice] segments have vocal cord vibration. -/
  | voice
  /-- [+spread glottis] segments, such as [h] and aspirated stops, have a wide glottis. -/
  | spreadGlottis
  /-- [+constricted glottis] segments, such as the glottal stop and ejectives, have a narrow or
  closed glottis. -/
  | constrGlottis
  /-- [+labial] segments are articulated with the lips. -/
  | labial
  /-- [+round] segments are articulated with rounded lips. -/
  | round
  /-- [+labiodental] segments are articulated by touching the lower lip to the upper teeth. -/
  | labiodental
  /-- [+coronal] segments are articulated with the tongue blade or tip. -/
  | coronal
  /-- [+anterior] coronals are articulated at the alveolar ridge or further forward. -/
  | anterior
  /-- [+distributed] coronals are laminal, made with the tongue blade, and [−distributed] ones
  apical. -/
  | distributed
  /-- [+dorsal] segments are articulated with the tongue body. -/
  | dorsal
  /-- [+high] vowels and dorsals have the tongue body raised. -/
  | high
  /-- [+low] vowels and dorsals have the tongue body lowered. -/
  | low
  /-- [+front] vowels and dorsals are front; central ones are [−front, −back]. -/
  | front
  /-- [+back] vowels and dorsals are back; central ones are [−front, −back]. -/
  | back
  /-- [tense] divides the high and the mid vowels in two, [−tense] ones being lax. -/
  | tense
  /-- [+ATR] segments have the tongue root advanced. -/
  | atr
  /-- [+RTR] segments have the tongue root retracted. -/
  | rtr
  deriving DecidableEq, Repr

namespace Feature

/-- All features, in declaration order. -/
def allFeatures : List Feature :=
  [.syllabic, .consonantal, .sonorant, .approximant,
   .continuant, .delayedRelease, .nasal, .lateral, .strident, .tap, .trill,
   .voice, .spreadGlottis, .constrGlottis,
   .labial, .round, .labiodental,
   .coronal, .anterior, .distributed,
   .dorsal, .high, .low, .front, .back, .tense, .atr, .rtr]

instance : Fintype Feature where
  elems := ⟨allFeatures, by decide⟩
  complete f := by cases f <;> decide

end Feature

/-! ### Segments -/

/-- A segment: each feature `+`, `−` or unspecified. A structure and not the type of functions
itself, so that the order and the instances of function types do not apply to segments: the
order on segments is inclusion of feature matrices, and the segments are not enumerated as a
finite type when a statement about the members of an inventory is decided. -/
@[ext] structure Segment where
  /-- The value a segment gives each feature. -/
  val : Feature → Option Bool

namespace Segment

instance : CoeFun Segment fun _ ↦ Feature → Option Bool := ⟨val⟩

@[simp] theorem mk_apply (v : Feature → Option Bool) (f : Feature) : (⟨v⟩ : Segment) f = v f := rfl

/-- Two segments with the same value for every feature are equal. -/
theorem ext' {s t : Segment} (h : ∀ f, s f = t f) : s = t := Segment.ext (funext h)

instance instDecidableEq : DecidableEq Segment := fun s t ↦
  decidable_of_iff (s.val = t.val) Segment.ext_iff.symm

variable (s : Segment)

/-- The feature matrix with no values. -/
instance : Bot Segment := ⟨⟨fun _ ↦ none⟩⟩

instance : Inhabited Segment := ⟨⊥⟩

@[simp] theorem bot_apply (f : Feature) : (⊥ : Segment) f = none := rfl

/-- `d ≤ s` holds when `s` has every value that `d` has: the matrix of `s` includes the matrix
`d`, as a segment includes the matrices of a rule that applies to it. -/
instance : LE Segment := ⟨fun d s ↦ ∀ f v, d f = some v → s f = some v⟩

theorem le_def {d s : Segment} : d ≤ s ↔ ∀ f v, d f = some v → s f = some v := Iff.rfl

instance : DecidableLE Segment := fun d s ↦
  inferInstanceAs (Decidable (∀ f v, d f = some v → s f = some v))

end Segment

/-! ### Feature matrices -/

/-- A feature value in a feature matrix: `+nasal` or `−voice`. -/
declare_syntax_cat featureValue
/-- The value `+` of a feature. -/
syntax "+" ident : featureValue
/-- The value `−` of a feature. -/
syntax "−" ident : featureValue
/-- The value `−` of a feature, written with a hyphen. -/
syntax "-" ident : featureValue

/-- `[+nasal, −voice]` is the segment with those feature values and no others, the feature
matrix of a rule or of a natural class. A feature may be named only once. -/
scoped syntax (name := featureMatrix) "[" featureValue,+ "]" : term

open Lean in
macro_rules
  | `([$vs:featureValue,*]) => do
    let parsed ← vs.getElems.mapM fun v ↦ match v with
      | `(featureValue| +$f:ident) => pure (f, true)
      | `(featureValue| −$f:ident) => pure (f, false)
      | `(featureValue| -$f:ident) => pure (f, false)
      | _ => Macro.throwUnsupported
    let mut seen : Array Name := #[]
    for (f, _) in parsed do
      if seen.contains f.getId then
        Macro.throwErrorAt f s!"the feature [{f.getId}] is named twice"
      seen := seen.push f.getId
    let body ← parsed.foldrM (fun (f, b) acc ↦ do
      let feat := mkIdentFrom f (`Phonology.Feature ++ f.getId)
      let val ← if b then `(true) else `(false)
      `($(mkCIdent `Phonology.Segment.setFeature) $acc $feat $val))
      (← `((⊥ : $(mkCIdent `Phonology.Segment))))
    `($body)

namespace Segment

variable (s : Segment)

/-! ### Natural classes -/

/-- A segment is syllabic when it is [+syllabic], the nucleus of its syllable, as a vowel, a
syllabic liquid or a syllabic nasal is. -/
def IsSyllabic : Prop := s .syllabic = true
instance : Decidable s.IsSyllabic := inferInstanceAs (Decidable (_ = _))

/-- A vowel is a [+syllabic, −consonantal] segment, which the syllabic liquids and nasals are not
([hayes-2009], Table 4.1 and §4.4.3). -/
def IsVowel : Prop := s.IsSyllabic ∧ s .consonantal = false
instance : Decidable s.IsVowel := inferInstanceAs (Decidable (_ ∧ _))

/-- A consonant is a [+consonantal] segment. -/
def IsConsonant : Prop := s .consonantal = true
instance : Decidable s.IsConsonant := inferInstanceAs (Decidable (_ = _))

/-- An obstruent is a [−sonorant] segment. -/
def IsObstruent : Prop := s .sonorant = false
instance : Decidable s.IsObstruent := inferInstanceAs (Decidable (_ = _))

/-- A nasal is a [−approximant, +sonorant] segment. -/
def IsNasal : Prop := s .approximant = false ∧ s .sonorant = true
instance : Decidable s.IsNasal := inferInstanceAs (Decidable (_ ∧ _))

/-- A sibilant is a [+strident] segment. -/
def IsSibilant : Prop := s .strident = true
instance : Decidable s.IsSibilant := inferInstanceAs (Decidable (_ = _))

/-! ### Changes -/

/-- The segment with feature `f` set to `v`, whatever its value before. -/
def setFeature (f : Feature) (v : Bool) : Segment := ⟨Function.update s f (some v)⟩

/-- The segment with the values of `d` where it has them and those of `s` elsewhere, as when
`s` undergoes the change `A → d` of a rule. -/
protected def or (d s : Segment) : Segment := ⟨fun f ↦ (d f).or (s f)⟩

@[simp] theorem or_apply (d s : Segment) (f : Feature) : d.or s f = (d f).or (s f) := rfl

/-- The segment kept on the features in `C` and unspecified on the rest. -/
def restrict (C : Finset Feature) (s : Segment) : Segment := ⟨C.piecewise s fun _ ↦ none⟩

/-- The segment with the values of `s` on the features in `C` and those of `t` on the rest, as
when `t` takes a class of features from `s`. -/
def piecewise (C : Finset Feature) (s t : Segment) : Segment := ⟨C.piecewise s t⟩

@[simp] theorem coe_piecewise (C : Finset Feature) (s t : Segment) :
    ⇑(piecewise C s t) = C.piecewise s t := rfl

end Segment

/-- The classification of a segment as a consonant or a vowel. -/
inductive Segment.Class where
  /-- A consonant. -/
  | consonant
  /-- A vowel. -/
  | vowel
  deriving DecidableEq, Repr, Fintype

end Phonology
