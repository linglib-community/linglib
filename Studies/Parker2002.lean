module

public import Linglib.Phonology.Segmental.NaturalClass
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.Order

/-!
# Parker (2002): the sonority hierarchy

Parker measures the acoustic correlates of sonority and proposes a universal hierarchy of sixteen
classes (Table 5.28), which languages conflate by merging adjacent classes. The modal hierarchy
of five classes, Clements's, is such a conflation (`toSonority_monotone`).

Within the obstruents, fricatives outrank stops and voiced obstruents voiceless ones, two orders
Parker takes as fixed. An obstruent class is its values of [continuant] and [voice], and the two
orders together are the product order. A ranking strictly monotone for it is then fixed by how it
compares the voiceless fricatives with the voiced stops, so that (3.6) lists every such ranking
(`le_iff_hierarchy_le`). However the classes are ranked, [continuant] and [voice] do not both
divide them into contiguous classes (`not_contiguous_continuant_and_voice`): (3.6a) keeps those of
[continuant] contiguous, Parker's default (3.6b) those of [voice], and the tie (3.6c) none
(`contiguous_hierarchy`). Unlike the four features of the modal hierarchy, then, [continuant] and
[voice] cannot both cut the sonority hierarchy at one point.

## Main definitions

* `Parker2002.Obstruent`: an obstruent class, by its values of [continuant] and [voice], ordered
  by the product order.
* `Parker2002.hierarchy`: the rankings of the obstruents in (3.6), indexed by how they compare
  the voiceless fricatives with the voiced stops.
* `Parker2002.Class`, `Parker2002.Class.rankWith`: the classes of Table 5.28 and their ranks, with
  the obstruents ranked by a hierarchy of (3.6); `Class.rank` takes Parker's default.
* `Parker2002.Contiguous`: a set of obstruent classes is contiguous on a ranking, that is, the
  preimage of an order-connected set (`contiguous_iff_exists_ordConnected`).

## References

* [parker-2002]: the modal hierarchy (3.3) (p. 62), the obstruent hierarchies (3.6) and their
  adherents (3.7) (pp. 68–70), the placement of /h/ and English /r/ (pp. 237–238), and Table 5.28
  (p. 240)
-/

@[expose] public section

namespace Parker2002

open Phonology

/-! ### Obstruent classes -/

/-- An obstruent class, by its values of [continuant] and [voice]. -/
@[ext]
structure Obstruent where
  /-- Whether the class is [+continuant], a class of fricatives. -/
  continuant : Bool
  /-- Whether the class is [+voice]. -/
  voice : Bool
  deriving DecidableEq, Repr, Fintype, Inhabited

namespace Obstruent

/-- The voiceless stops and affricates. -/
def voicelessStop : Obstruent := ⟨false, false⟩

/-- The voiceless fricatives. -/
def voicelessFricative : Obstruent := ⟨true, false⟩

/-- The voiced stops and affricates. -/
def voicedStop : Obstruent := ⟨false, true⟩

/-- The voiced fricatives. -/
def voicedFricative : Obstruent := ⟨true, true⟩

/-- A class as its pair of values. -/
def toProd (o : Obstruent) : Bool × Bool := (o.continuant, o.voice)

theorem toProd_injective : Function.Injective toProd := fun _ _ h ↦
  Obstruent.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- The product order, which puts fricatives above stops and voiced obstruents above voiceless
ones, the two orders Parker takes as fixed. -/
instance : PartialOrder Obstruent := PartialOrder.lift toProd toProd_injective

instance : DecidableLE Obstruent := fun a b ↦
  inferInstanceAs (Decidable (a.continuant ≤ b.continuant ∧ a.voice ≤ b.voice))

instance : DecidableLT Obstruent := decidableLTOfDecidableLE

/-- The features of a class. -/
def column (o : Obstruent) : Segment :=
  .ofSpecs [(.sonorant, false), (.continuant, o.continuant), (.voice, o.voice)]

end Obstruent

open Obstruent

/-- The ranking of the obstruent classes in (3.6) that compares the voiceless fricatives with the
voiced stops by `o`: below them for `lt` (3.6b), level with them for `eq` (3.6c), and above them
for `gt` (3.6a). -/
def hierarchy (o : Ordering) : Obstruent → ℕ
  | ⟨false, false⟩ => 1
  | ⟨true, false⟩ => if o = .gt then 3 else 2
  | ⟨false, true⟩ => if o = .lt then 3 else 2
  | ⟨true, true⟩ => 4

/-- The hierarchies of (3.6) keep fricatives above stops and voiced obstruents above voiceless
ones. -/
theorem strictMono_hierarchy (o : Ordering) : StrictMono (hierarchy o) := by
  revert o
  simp only [StrictMono]
  decide +kernel

/-- (3.6) is exhaustive: a ranking that keeps fricatives above stops and voiced obstruents above
voiceless ones orders the classes as the hierarchy fixed by how it compares the voiceless
fricatives with the voiced stops. -/
theorem le_iff_hierarchy_le {α : Type*} [LinearOrder α] {r : Obstruent → α} (hr : StrictMono r)
    (x y : Obstruent) :
    r x ≤ r y ↔ hierarchy (compare (r voicelessFricative) (r voicedStop)) x ≤
      hierarchy (compare (r voicelessFricative) (r voicedStop)) y := by
  have h₁ : r voicelessStop < r voicelessFricative := hr (by decide)
  have h₂ : r voicelessStop < r voicedStop := hr (by decide)
  have h₃ : r voicelessFricative < r voicedFricative := hr (by decide)
  have h₄ : r voicedStop < r voicedFricative := hr (by decide)
  simp only [voicelessStop, voicelessFricative, voicedStop, voicedFricative] at *
  rcases lt_trichotomy (r ⟨true, false⟩) (r ⟨false, true⟩) with h | h | h <;>
    [rw [compare_lt_iff_lt.2 h]; rw [compare_eq_iff_eq.2 h]; rw [compare_gt_iff_gt.2 h]] <;>
    rcases x with ⟨_ | _, _ | _⟩ <;> rcases y with ⟨_ | _, _ | _⟩ <;> simp [hierarchy] <;> order

/-! ### The hierarchy -/

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

/-- The rank of a class in Table 5.28, with the obstruents ranked by the hierarchy of (3.6) that
`o` fixes. -/
def rankWith (o : Ordering) : Class → ℕ
  | obstruent x => hierarchy o x
  | h => 5 | nasal => 6 | trill => 7 | flap => 8 | lateral => 9 | rhotic => 10 | glide => 11
  | highCentral => 12 | schwa => 13 | high => 14 | mid => 15 | low => 16

/-- The rank of a class in Table 5.28, with voiced stops above voiceless fricatives, Parker's
default (3.6b). -/
def rank : Class → ℕ := rankWith .lt

theorem rank_injective : Function.Injective rank := by decide +kernel

/-- Table 5.28 in Parker's default order (3.6b). -/
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

/-! ### Contiguity -/

variable {α : Type*} [LinearOrder α]

/-- A set of obstruent classes is contiguous on a ranking when every class ranked between two of
its members belongs to it. -/
def Contiguous (r : Obstruent → α) (S : Set Obstruent) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c, r a ≤ r c → r c ≤ r b → c ∈ S

instance (r : Obstruent → α) (S : Set Obstruent) [DecidablePred (· ∈ S)] :
    Decidable (Contiguous r S) := by
  unfold Contiguous; infer_instance

/-- A set is contiguous exactly when it is the preimage of an order-connected set. -/
theorem contiguous_iff_exists_ordConnected {r : Obstruent → α} {S : Set Obstruent} :
    Contiguous r S ↔ ∃ I : Set α, I.OrdConnected ∧ S = r ⁻¹' I := by
  refine ⟨fun h ↦ ⟨{x | ∃ a ∈ S, ∃ b ∈ S, r a ≤ x ∧ x ≤ r b}, ⟨?_⟩, ?_⟩, ?_⟩
  · rintro x ⟨a, ha, -, -, hax, -⟩ y ⟨-, -, b, hb, -, hyb⟩ z ⟨hxz, hzy⟩
    exact ⟨a, ha, b, hb, hax.trans hxz, hzy.trans hyb⟩
  · ext c
    exact ⟨fun hc ↦ ⟨c, hc, c, hc, le_rfl, le_rfl⟩,
      fun ⟨a, ha, b, hb, hac, hcb⟩ ↦ h a ha b hb c hac hcb⟩
  · rintro ⟨I, hI, rfl⟩ a ha b hb c hac hcb
    exact hI.out ha hb ⟨hac, hcb⟩

/-- The classes that [continuant] and [voice] pick out are natural classes of the obstruents. -/
example (v : Bool) :
    IsNaturalClass (Finset.univ.image column)
        ((Finset.univ.filter (·.continuant = v)).image column) ∧
      IsNaturalClass (Finset.univ.image column)
        ((Finset.univ.filter (·.voice = v)).image column) := by
  revert v
  decide +kernel

/-- However the obstruent classes are ranked, ties allowed, [continuant] and [voice] do not both
divide them into contiguous classes: a class of least rank shares [continuant] with one of its
neighbours and [voice] with the other, and the lower of the two lies between it and the other. -/
theorem not_contiguous_continuant_and_voice (r : Obstruent → α) :
    ¬ ((∀ v, Contiguous r {o | o.continuant = v}) ∧ ∀ v, Contiguous r {o | o.voice = v}) := by
  rintro ⟨hc, hv⟩
  obtain ⟨m, hm⟩ := Finite.exists_min r
  rcases le_total (r ⟨!m.continuant, m.voice⟩) (r ⟨m.continuant, !m.voice⟩) with h | h
  · simpa using hc m.continuant m rfl ⟨m.continuant, !m.voice⟩ rfl _ (hm _) h
  · simpa using hv m.voice m rfl ⟨!m.continuant, m.voice⟩ rfl _ (hm _) h

/-- Hierarchy (3.6a) keeps the classes of [continuant] contiguous, Parker's default (3.6b) those
of [voice], and the tie (3.6c) none of the four. -/
theorem contiguous_hierarchy (v : Bool) :
    (Contiguous (hierarchy .gt) {o | o.continuant = v} ∧
      ¬ Contiguous (hierarchy .gt) {o | o.voice = v}) ∧
    (¬ Contiguous (hierarchy .lt) {o | o.continuant = v} ∧
      Contiguous (hierarchy .lt) {o | o.voice = v}) ∧
    ¬ Contiguous (hierarchy .eq) {o | o.continuant = v} ∧
      ¬ Contiguous (hierarchy .eq) {o | o.voice = v} := by
  revert v
  decide +kernel

end Parker2002
