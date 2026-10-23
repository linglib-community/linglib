module

public import Linglib.Phonology.Segmental.NaturalClass
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Pi

/-!
# Parker (2002): the sonority hierarchy

Parker measures the acoustic correlates of sonority and proposes a universal hierarchy of sixteen
classes (Table 5.28), which languages conflate by merging adjacent classes. The modal hierarchy
of five classes, Clements's, is such a conflation (`toSonority_monotone`).

Within the obstruents, fricatives outrank stops and voiced obstruents voiceless ones, two orders
Parker takes as fixed. An obstruent class is its values of [continuant] and [voice], the two
orders together are the product order, and the hierarchies of (3.6) are the rankings strictly
monotone for it (`strictMono_hierarchy`), which leave open only whether voiced stops outrank
voiceless fricatives. No ranking of the four classes, ties allowed, keeps all four of the classes
that [continuant] and [voice] pick out contiguous (`exists_not_contiguous`): (3.6a) keeps those of
[continuant], Parker's default (3.6b), which `Class.rank` follows, those of [voice], and the tie
(3.6c) none (`contiguous_hierarchy`). Unlike the four features of the modal hierarchy, then,
[continuant] and [voice] cannot both cut the sonority hierarchy at one point.

## Main definitions

* `Parker2002.Obstruent`: an obstruent class, by its values of [continuant] and [voice].
* `Parker2002.hierarchy`: the three rankings of the obstruents in (3.6).
* `Parker2002.Class`, `Parker2002.Class.rankWith`: the classes of Table 5.28 and their ranks, with
  the obstruents ranked by a hierarchy of (3.6); `Class.rank` takes Parker's default.
* `Parker2002.Contiguous`: a set of obstruent classes is contiguous on a ranking.

## References

* [parker-2002]: the modal hierarchy (3.3) (p. 62), the obstruent hierarchies (3.6) and their
  adherents (3.7) (pp. 68–70), the placement of /h/ and English /r/ (pp. 237–238), and Table 5.28
  (p. 240)
-/

@[expose] public section

namespace Parker2002

open Phonology

/-! ### The hierarchy -/

/-- An obstruent class: its values of [continuant] and [voice], so that `(false, false)` is the
voiceless stops and affricates and `(true, true)` the voiced fricatives. The product order puts
fricatives above stops and voiced obstruents above voiceless ones. -/
abbrev Obstruent := Bool × Bool

/-- The features of an obstruent class. -/
def Obstruent.column (o : Obstruent) : Segment :=
  .ofSpecs [(.sonorant, false), (.continuant, o.1), (.voice, o.2)]

/-- The rankings of the obstruents in (3.6): voiceless fricatives above voiced stops (a), below
them (b), or level with them (c). -/
def hierarchy : Fin 3 → Obstruent → ℕ
  | 0 => fun | (false, false) => 1 | (false, true) => 2 | (true, false) => 3 | (true, true) => 4
  | 1 => fun | (false, false) => 1 | (true, false) => 2 | (false, true) => 3 | (true, true) => 4
  | 2 => fun | (false, false) => 1 | (true, false) => 2 | (false, true) => 2 | (true, true) => 3

/-- The sonority classes of Table 5.28. -/
inductive Class where
  /-- The obstruents of a class. -/
  | obstruent (o : Obstruent)
  /-- /h/. -/
  | h
  /-- The nasals. -/
  | nasal
  /-- The trills. -/
  | trill
  /-- The flaps. -/
  | flap
  /-- The laterals. -/
  | lateral
  /-- English /r/. -/
  | rhotic
  /-- The glides. -/
  | glide
  /-- /ɨ/. -/
  | highCentral
  /-- /ə/. -/
  | schwa
  /-- The high vowels other than /ɨ/. -/
  | high
  /-- The mid vowels other than /ə/. -/
  | mid
  /-- The low vowels. -/
  | low
  deriving DecidableEq, Repr, Fintype

namespace Class

/-- The rank of a class in Table 5.28, with the obstruents ranked by hierarchy `i` of (3.6). -/
def rankWith (i : Fin 3) : Class → ℕ
  | obstruent o => hierarchy i o
  | h => 5 | nasal => 6 | trill => 7 | flap => 8 | lateral => 9 | rhotic => 10 | glide => 11
  | highCentral => 12 | schwa => 13 | high => 14 | mid => 15 | low => 16

/-- The rank of a class in Table 5.28, with voiced stops above voiceless fricatives, Parker's
default (3.6b). -/
def rank : Class → ℕ := rankWith 1

theorem rank_injective : Function.Injective rank := by decide +kernel

instance : LinearOrder Class := LinearOrder.lift' rank rank_injective

/-- The class of the modal hierarchy that a class falls in, with /h/ among the obstruents. -/
def toSonority : Class → Sonority
  | obstruent _ | h => .obstruent
  | nasal => .nasal
  | trill | flap | lateral | rhotic => .liquid
  | glide => .glide
  | highCentral | schwa | high | mid | low => .vowel

/-- The modal hierarchy conflates Table 5.28, merging adjacent classes. -/
theorem toSonority_monotone : Monotone toSonority := by
  intro a b
  change a.rank ≤ b.rank → _
  revert a b
  decide +kernel

end Class

/-! ### Contiguity of the obstruent classes -/

/-- A set of obstruent classes is contiguous on a ranking when every class ranked between two of
its members belongs to it. -/
def Contiguous (r : Obstruent → ℕ) (S : Finset Obstruent) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c, r a ≤ r c → r c ≤ r b → c ∈ S

instance (r : Obstruent → ℕ) (S : Finset Obstruent) : Decidable (Contiguous r S) := by
  unfold Contiguous; infer_instance

/-- The obstruent classes with value `v` for feature `f`. -/
def featureClass (f : Feature) (v : Bool) : Finset Obstruent :=
  Finset.univ.filter fun o ↦ (Obstruent.column o).HasValue f v

/-- The classes that [continuant] and [voice] pick out are natural classes of the obstruents. -/
example : ∀ f ∈ [Feature.continuant, .voice], ∀ v,
    IsNaturalClass (Finset.univ.image Obstruent.column)
      ((featureClass f v).image Obstruent.column) := by
  decide +kernel

/-- However the four obstruent classes are ranked, ties allowed, one of the classes that
[continuant] or [voice] picks out is not contiguous. -/
theorem exists_not_contiguous (r : Obstruent → Fin 4) :
    ∃ f ∈ [Feature.continuant, .voice], ∃ v, ¬ Contiguous (fun o ↦ r o) (featureClass f v) := by
  revert r
  decide +kernel

/-- The hierarchies of (3.6) are the rankings strictly monotone for the product order, which
keep fricatives above stops and voiced obstruents above voiceless ones. -/
theorem strictMono_hierarchy (i : Fin 3) : StrictMono (hierarchy i) := by
  revert i
  simp only [StrictMono, Prod.lt_iff]
  decide +kernel

/-- Hierarchy (3.6a) keeps the classes of [continuant] contiguous, Parker's default (3.6b) those
of [voice], and the tie (3.6c) none of the four. -/
theorem contiguous_hierarchy :
    (∀ v, Contiguous (hierarchy 0) (featureClass .continuant v) ∧
      ¬ Contiguous (hierarchy 0) (featureClass .voice v)) ∧
    (∀ v, ¬ Contiguous (hierarchy 1) (featureClass .continuant v) ∧
      Contiguous (hierarchy 1) (featureClass .voice v)) ∧
    ∀ f ∈ [Feature.continuant, .voice], ∀ v, ¬ Contiguous (hierarchy 2) (featureClass f v) := by
  decide +kernel

end Parker2002
