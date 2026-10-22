/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Order.Nat
public import Mathlib.Data.Finset.Piecewise
public import Linglib.Core.Order.Flat

/-!
# Segmental representation: definitions

The distinctive feature and the segment built over it. A **feature** is one of the
26 binary distinctive features of Hayes's chart, or one of the tongue-root features
[ATR] and [RTR] of Halle, Vaux and Wolfe; a **segment** is a partial
specification of those features — each `+`, `−`, or unspecified — ordered by
specificity (the unification-grammar subsumption order, inherited as a feature
bundle), with the unspecified archisegment least and natural-class generalization
as meet.

This file collects definitions only — the feature inventory, the segment and its
valuation/construction/change API, the natural-class predicates, and the sonority
scales. The theorems about them live in `Phonology/Segmental/Basic.lean`.

## References

* [hayes-2009]
* [halle-vaux-wolfe-2000]
* [chomsky-halle-1968]
* [clements-1990]
* [parker-2002]
* [keating-1988]
* [archangeli-1988]
* [kiparsky-1982]
* [inkelas-orgun-1995]
* [steriade-1995]
* [sen-2015]
* [afkir-zellou-2025]
-/

@[expose] public section

namespace Phonology

/-! ### Feature inventory -/

/-- A binary distinctive phonological feature, following [hayes-2009]'s segmental
    inventory. (The stress and length features are excluded: [hayes-2009] treats
    stress as a syllable-level property, not a segmental feature.) [ATR], the
    tongue-root feature of the sub-Saharan harmony systems, is the one feature
    [hayes-2009] names among the vowel features but leaves off his chart, noting
    that whether it is the same feature as [tense] is unsettled; it is kept
    distinct here. [RTR], the other tongue-root feature of [halle-vaux-wolfe-2000],
    distinguishes the pharyngealized consonants, which the PHOIBLE chart codes by it. The
    grouping of the features into classes is `Phonology.FeatureClass`. -/
inductive Feature where
  | syllabic         -- [+syll] = vowels
  | consonantal      -- [+cons] = oral constriction
  | sonorant         -- [+son] = spontaneous voicing
  | approximant      -- [+approx] = no turbulence
  | continuant       -- [+cont] = airflow continues
  | delayedRelease   -- [+del.rel.] = affricates
  | nasal            -- [+nasal] = lowered velum
  | lateral          -- [+lat] = lateral airflow
  | strident         -- [+strid] = high-amplitude noise
  | tap              -- [+tap] = ballistic gesture
  | trill            -- [+trill] = aerodynamic vibration
  | voice            -- [+voice] = vocal cord vibration
  | spreadGlottis    -- [+s.g.] = aspiration
  | constrGlottis    -- [+c.g.] = glottal constriction
  | labial           -- [+lab] = lips involved
  | round            -- [+round] = lip rounding
  | labiodental      -- [+labiodental] = lower lip to upper teeth
  | coronal          -- [+cor] = tongue blade/tip
  | anterior         -- [+ant] = alveolar ridge or forward
  | distributed      -- [+dist] = laminal contact
  | dorsal           -- [+dor] = tongue body
  | high             -- tongue body raised
  | low              -- tongue body lowered
  | front            -- tongue body fronted
  | back             -- tongue body backed
  | tense            -- tense vowel quality
  | atr              -- [+ATR] = advanced tongue root
  | rtr              -- [+RTR] = retracted tongue root
  deriving DecidableEq, Repr

namespace Feature

/-! ### Enumeration -/

/-- All features, in declaration order. -/
def allFeatures : List Feature :=
  [.syllabic, .consonantal, .sonorant, .approximant,
   .continuant, .delayedRelease, .nasal, .lateral, .strident, .tap, .trill,
   .voice, .spreadGlottis, .constrGlottis,
   .labial, .round, .labiodental,
   .coronal, .anterior, .distributed,
   .dorsal, .high, .low, .front, .back, .tense, .atr, .rtr]

/-- `allFeatures` is the canonical enumeration: completeness is the `Fintype` law,
not a theorem re-proved beside it. -/
instance : Fintype Feature where
  elems := ⟨allFeatures, by decide⟩
  complete f := by cases f <;> decide

end Feature

/-! ### The segment bundle -/

/-- A **segment**: a partial specification of the distinctive features — each
    feature is `+`, `−`, or left unspecified. Segments are ordered by specificity:
    one refines another when it agrees on every feature the other commits to, and
    possibly more. The fully unspecified segment is least; the most specific class
    common to two segments is their meet. -/
abbrev Segment := Feature → Flat Bool

namespace Segment

variable (s : Segment)

/-! ### Valuation -/

/-- Does feature `f` have value `v`? -/
def HasValue (f : Feature) (v : Bool) : Prop := s f = some v

instance (f : Feature) (v : Bool) : Decidable (s.HasValue f v) :=
  inferInstanceAs (Decidable (_ = _))

/-- A segment is **unspecified** for feature `f` iff its value there is `none`. -/
def Unspecified (f : Feature) : Prop := s f = none

instance (f : Feature) : Decidable (s.Unspecified f) := inferInstanceAs (Decidable (_ = none))

/-! ### Construction -/

/-- The segment read off a list of (feature, value) pairs. Unmentioned features are
    unspecified, giving natural-class semantics:
    `ofSpecs [(continuant, false)]` lies below every [−cont] segment. -/
def ofSpecs (specs : List (Feature × Bool)) : Segment := fun f ↦ specs.lookup f

/-! ### Natural-class predicates

Language-neutral natural-class membership predicates, by the SPE feature
decompositions standard since [chomsky-halle-1968] and codified in textbook form
by [hayes-2009]. Pure substrate: they project information already encoded in a
segment, consumed by per-language Fragment files rather than redefined locally. -/

/-- A segment is a vowel iff it is [+syllabic]. -/
def IsVowel : Prop := s.HasValue .syllabic true
instance : Decidable s.IsVowel := by unfold IsVowel; infer_instance

/-- A segment is a consonant iff it is [+consonantal]. -/
def IsConsonant : Prop := s.HasValue .consonantal true
instance : Decidable s.IsConsonant := by unfold IsConsonant; infer_instance

/-- A segment is an obstruent iff it is [+cons, -son]. -/
def IsObstruent : Prop := s.HasValue .consonantal true ∧ s.HasValue .sonorant false
instance : Decidable s.IsObstruent := by unfold IsObstruent; infer_instance

/-- A segment is an oral stop iff it is [+cons, -son, -cont]. -/
def IsStop : Prop :=
  s.HasValue .consonantal true ∧ s.HasValue .sonorant false ∧ s.HasValue .continuant false
instance : Decidable s.IsStop := by unfold IsStop; infer_instance

/-- A segment is a fricative iff it is [+cons, -son, +cont]. -/
def IsFricative : Prop :=
  s.HasValue .consonantal true ∧ s.HasValue .sonorant false ∧ s.HasValue .continuant true
instance : Decidable s.IsFricative := by unfold IsFricative; infer_instance

/-- A segment is a nasal iff it is [+nasal]. -/
def IsNasal : Prop := s.HasValue .nasal true
instance : Decidable s.IsNasal := by unfold IsNasal; infer_instance

/-- A segment is a liquid iff it is [+cons, +son] and one of [+lateral], [+trill],
    [+tap] — the lateral /l/, the trill /r/, and the flap /ɾ/ under one class. -/
def IsLiquid : Prop :=
  s.HasValue .consonantal true ∧ s.HasValue .sonorant true ∧
    (s.HasValue .lateral true ∨ s.HasValue .trill true ∨ s.HasValue .tap true)
instance : Decidable s.IsLiquid := by unfold IsLiquid; infer_instance

/-- A segment is a sibilant iff it is [+strident]. [strident] is a coronal feature, so the
    sibilants are the strident coronal fricatives and affricates. -/
def IsSibilant : Prop := s.HasValue .strident true
instance : Decidable s.IsSibilant := inferInstanceAs (Decidable (s.HasValue _ _))

/-- A segment is a glide iff it is [-cons, -syllabic, +approximant]. -/
def IsGlide : Prop :=
  s.HasValue .consonantal false ∧ s.HasValue .syllabic false ∧ s.HasValue .approximant true
instance : Decidable s.IsGlide := by unfold IsGlide; infer_instance

/-! ### Feature changes

Three-valued (`+ / − / ∅`) specification is standard in [keating-1988],
[inkelas-orgun-1995], and [steriade-1995]; `fillFromContext` is default-fill,
preserving existing values per [kiparsky-1982] [archangeli-1988], while
`setFeature` overrides. The Latin coda /l/ analysis in [sen-2015] is a worked
example. -/

/-- Set feature `f` to value `v`, overriding any existing specification. For default-fill
    semantics that only assign when `f` is currently unspecified, use `fillFromContext`. -/
def setFeature (f : Feature) (v : Bool) : Segment := Function.update s f (some v)

/-- In categorical feature spreading from context, the target `s`, when unspecified
    for `f`, takes the `f`-value of `ctx`, and already-specified targets and features
    other than `f` are untouched. When `ctx` is itself unspecified for `f`, the
    target stays unspecified.

    This is a [keating-1988] *context rule*: the target acquires a categorical
    feature value from its neighbour and that value blocks further interactions.
    It is **distinct from** her gradient phonetic interpolation (her unspecified
    /h/ example), in which an unspecified segment stays unspecified and the
    phonetics builds a continuous trajectory through it; gradient phonetic
    interpolation is out of scope at this categorical-featural substrate. -/
def fillFromContext (f : Feature) (ctx : Segment) : Segment :=
  fun g ↦ (s g).or (Function.update (⊥ : Segment) f (ctx f) g)

/-- The segment kept on the features in `C` and unspecified on the rest. -/
def restrict (C : Finset Feature) (s : Segment) : Segment := C.piecewise s ⊥

end Segment

/-- The coarse two-way classification of a segment, the commonest conditioning
environment for morph-variant selection (pre-consonantal vs pre-vocalic). -/
inductive Segment.Class where
  /-- A consonant. -/
  | consonant
  /-- A vowel. -/
  | vowel
  deriving DecidableEq, Repr, Fintype

/-- A segment's coarse class is vowel when it is [+syllabic] and consonant otherwise. -/
def Segment.toClass (s : Segment) : Segment.Class :=
  if s.IsVowel then .vowel else .consonant

/-! ### Sonority -/

/-- The abstract sonority hierarchy ([clements-1990]): what the synchronic grammar
    operates on, ordering segments from least to most sonorous.

    | Rank | Class     |
    |------|-----------|
    |  0   | Stop      |
    |  1   | Fricative |
    |  2   | Nasal     |
    |  3   | Liquid    |
    |  4   | Glide     |
    |  5   | Vowel     |

    For the finer 8-level scale that splits obstruents by voice, see
    `Sonority.Class`. -/
inductive Sonority where
  | stop
  | fricative
  | nasal
  | liquid
  | glide
  | vowel
  deriving DecidableEq, Repr

namespace Sonority

/-- Numeric rank (0 = least sonorous). -/
def rank : Sonority → Nat
  | .stop => 0 | .fricative => 1 | .nasal => 2
  | .liquid => 3 | .glide => 4 | .vowel => 5

instance : LinearOrder Sonority :=
  LinearOrder.lift' rank fun a b h => by cases a <;> cases b <;> simp_all [rank]

/-- The sonority of a segment, read off its features ([hayes-2009], [clements-1990]). -/
def ofSegment (s : Segment) : Sonority :=
  if s.HasValue .sonorant false then
    if s.HasValue .continuant true then .fricative else .stop
  else if s.HasValue .approximant false then .nasal
  else if s.HasValue .consonantal true then .liquid
  else if s.HasValue .syllabic true then .vowel
  else .glide

/-! ### The Parker sonority scale -/

/-- The 8-level Parker sonority partition ([parker-2002]) — a refinement of
    `Sonority` that splits obstruents by [±continuant] and [±voice]. This is the
    sonority *scale*; it is distinct from the natural-class predicates above
    (`Segment.IsVowel` &c.), which are feature membership.

    Crucially [parker-2002] ranks voiced stops above voiceless fricatives
    (`vds = 3 > vlf = 2`) — his intensity-based default universal, reversible in
    particular languages. It is the scale on which sonority-conditioned variation
    such as Tarifit intrusive vowels is stated ([afkir-zellou-2025]). -/
inductive Class where
  | vls    -- voiceless stops: [−son, −cont, −voice]
  | vds    -- voiced stops: [−son, −cont, +voice]
  | vlf    -- voiceless fricatives: [−son, +cont, −voice]
  | vdf    -- voiced fricatives: [−son, +cont, +voice]
  | nasal  -- nasals: [+son, −approx]
  | liquid -- liquids/taps: [+son, +approx, +cons]
  | glide  -- glides: [+son, +approx, −cons, −syll]
  | vowel  -- vowels: [+son, +approx, −cons, +syll]
  deriving DecidableEq, Repr

/-- Parker's default universal 8-level ranking ([parker-2002]): voiced stops
    (`vds = 3`) outrank voiceless fricatives (`vlf = 2`). -/
def Class.parkerRank : Class → Nat
  | .vls => 1 | .vlf => 2 | .vds => 3 | .vdf => 4
  | .nasal => 5 | .liquid => 6 | .glide => 7 | .vowel => 8

/-- The voiceless obstruent classes. -/
def Class.Voiceless : Class → Prop
  | .vls | .vlf => True
  | _ => False

instance : DecidablePred Class.Voiceless := fun c =>
  match c with
  | .vls | .vlf => isTrue trivial
  | .vds | .vdf | .nasal | .liquid | .glide | .vowel => isFalse fun h => h

/-- A segment's class on the Parker eight-level scale refines `Sonority.ofSegment` by
    splitting the obstruents by [±voice] ([parker-2002]). -/
def Class.ofSegment (s : Segment) : Class :=
  if s.HasValue .sonorant false then
    if s.HasValue .continuant true then
      if s.HasValue .voice true then .vdf else .vlf
    else
      if s.HasValue .voice true then .vds else .vls
  else if s.HasValue .approximant false then .nasal
  else if s.HasValue .consonantal true then .liquid
  else if s.HasValue .syllabic true then .vowel
  else .glide

/-- Coarsen to the substance-free `Sonority`, collapsing the voicing split. -/
def Class.toSonority : Class → Sonority
  | .vls | .vds => .stop
  | .vlf | .vdf => .fricative
  | .nasal => .nasal
  | .liquid => .liquid
  | .glide => .glide
  | .vowel => .vowel

end Sonority

end Phonology
