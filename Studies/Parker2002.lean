module

public import Linglib.Phonology.Segmental.Sonority
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Sigma
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Tactic.Order

/-!
# Parker (2002): the sonority hierarchy

An obstruent class is a pair of values of [continuant] and [voice], and `Parker2002.Obstruent`
orders the four classes by the product order: fricatives above stops, voiced above voiceless,
with the voiceless fricatives and the voiced stops unordered. A ranking `r` of the four classes
in a linear order that is strictly monotone for the product order is determined, up to the order
it induces, by `compare (r voicelessFricative) (r voicedStop)`: it induces the order of
`Parker2002.hierarchy o` at that value `o` (`le_iff_hierarchy_le`), so there are three such
rankings.

`Parker2002.Class` is the sixteen sonority classes, the four obstruent classes below twelve
further classes in a chain. `Class.rankWith o` ranks them with the obstruents ranked by
`hierarchy o`; it is injective unless `o = .eq`. The order on `Class` is the one the rankings
share, `a ≤ b ↔ ∀ o, rankWith o a ≤ rankWith o b`, a partial order in which only the voiceless
fricatives and the voiced stops are unordered, and every strictly monotone ranking of the sixteen
classes induces the order of some `rankWith o` (`Class.le_iff_rankWith_le`).

`Class.toSonority` sends a class to its class in the hierarchy of obstruents, nasals, liquids,
glides and vowels. That hierarchy coarsens every `rankWith o` (`Class.coarsens_toSonority`), and
the classes it merges are contiguous on each.

On a strictly monotone ranking of the obstruents, the classes of [continuant] are contiguous
exactly when the voiceless fricatives outrank the voiced stops
(`contiguous_continuant_iff`), and those of [voice] exactly when the voiced stops outrank the
voiceless fricatives; on a tie neither are. On no ranking at all are both
(`not_contiguous_continuant_and_voice`).

## Implementation notes

The source's table of the sixteen classes lists the voiced stops and the voiceless fricatives at
two ranks in either order, the voiced stops higher by default. `Class.rankWith` takes the order
as an argument instead of fixing the default, and `Class` carries the partial order instead of a
linear one, so that a statement about `≤` holds on both rankings. The acoustic measurements and
the regression of sonority on intensity have no counterpart here.

## References

* [parker-2002]
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
@[simps]
def equivProd : Obstruent ≃ Bool × Bool where
  toFun o := (o.continuant, o.voice)
  invFun p := ⟨p.1, p.2⟩

/-- The product order, which puts fricatives above stops and voiced obstruents above voiceless
ones (p. 68). -/
instance : PartialOrder Obstruent := PartialOrder.lift equivProd equivProd.injective

instance : DecidableLE Obstruent := fun a b ↦
  inferInstanceAs (Decidable (a.continuant ≤ b.continuant ∧ a.voice ≤ b.voice))

instance : DecidableLT Obstruent := decidableLTOfDecidableLE

/-- `equivProd` as an order isomorphism. -/
@[simps!]
def orderIsoProd : Obstruent ≃o Bool × Bool where
  toEquiv := equivProd
  map_rel_iff' := .rfl

/-- The features of a class. -/
def column (o : Obstruent) : Segment :=
  (([−sonorant] : Segment).setFeature .continuant o.continuant).setFeature .voice o.voice

/-- The class of a segment, by its values of [continuant] and [voice]. -/
def ofSegment (s : Segment) : Obstruent :=
  ⟨decide (s .continuant = true), decide (s .voice = true)⟩

@[simp] theorem ofSegment_column (o : Obstruent) : ofSegment o.column = o := by
  revert o
  decide

end Obstruent

open Obstruent

/-- (3.6): the ranking of the obstruent classes that compares the voiceless fricatives with the
voiced stops by `o`: below them for `lt` (3.6b), level with them for `eq` (3.6c), and above them
for `gt` (3.6a). -/
def hierarchy (o : Ordering) : Obstruent → ℕ
  | ⟨false, false⟩ => 1
  | ⟨true, false⟩ => if o = .gt then 3 else 2
  | ⟨false, true⟩ => if o = .lt then 3 else 2
  | ⟨true, true⟩ => 4

theorem strictMono_hierarchy (o : Ordering) : StrictMono (hierarchy o) := by
  revert o
  simp only [StrictMono]
  decide +kernel

@[simp] theorem compare_hierarchy (o : Ordering) :
    compare (hierarchy o voicelessFricative) (hierarchy o voicedStop) = o := by
  cases o <;> rfl

/-- A ranking of the obstruent classes strictly monotone for the product order induces the order
of the hierarchy of (3.6) that compares the voiceless fricatives with the voiced stops as it
does. -/
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

/-- Table 5.28: the sonority classes. -/
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

/-- Table 5.28: the rank of a class, with the obstruents ranked by `hierarchy o`. The table as
printed is `rankWith .lt`, `rankWith .gt` exchanges its second and third ranks, and `rankWith .eq`
merges them. -/
def rankWith (o : Ordering) : Class → ℕ
  | obstruent x => hierarchy o x
  | h => 5 | nasal => 6 | trill => 7 | flap => 8 | lateral => 9 | rhotic => 10 | glide => 11
  | highCentral => 12 | schwa => 13 | high => 14 | mid => 15 | low => 16

theorem rankWith_injective {o : Ordering} (ho : o ≠ .eq) : Function.Injective (rankWith o) := by
  revert o
  decide +kernel

/-- The order the rankings of Table 5.28 share, in which only the voiceless fricatives and the
voiced stops are unordered (p. 241). -/
instance : PartialOrder Class :=
  PartialOrder.lift (fun c ↦ (rankWith .lt c, rankWith .gt c)) fun _ _ h ↦
    rankWith_injective (by decide) (congrArg Prod.fst h)

instance : DecidableLE Class := fun a b ↦
  inferInstanceAs (Decidable (rankWith .lt a ≤ rankWith .lt b ∧ rankWith .gt a ≤ rankWith .gt b))

instance : DecidableLT Class := decidableLTOfDecidableLE

theorem le_iff_forall_rankWith_le {a b : Class} : a ≤ b ↔ ∀ o, rankWith o a ≤ rankWith o b := by
  revert a b
  decide +kernel

@[simp] theorem obstruent_le_obstruent {x y : Obstruent} : obstruent x ≤ obstruent y ↔ x ≤ y := by
  revert x y
  decide

theorem strictMono_obstruent : StrictMono obstruent := by
  simp only [StrictMono]
  decide

theorem strictMono_rankWith (o : Ordering) : StrictMono (rankWith o) := by
  revert o
  simp only [StrictMono]
  decide +kernel

/-- A ranking of the classes strictly monotone for the shared order induces the order of the
ranking of Table 5.28 that compares the voiceless fricatives with the voiced stops as it does
(p. 241). -/
theorem le_iff_rankWith_le {α : Type*} [LinearOrder α] {r : Class → α} (hr : StrictMono r)
    (x y : Class) :
    r x ≤ r y ↔
      rankWith (compare (r (obstruent voicelessFricative)) (r (obstruent voicedStop))) x ≤
        rankWith (compare (r (obstruent voicelessFricative)) (r (obstruent voicedStop))) y := by
  have key : ∀ x y : Class, (∃ a b, x = obstruent a ∧ y = obstruent b) ∨ x ≤ y ∨ y ≤ x := by
    decide +kernel
  obtain ⟨a, b, rfl, rfl⟩ | h | h := key x y
  · exact le_iff_hierarchy_le (hr.comp strictMono_obstruent) a b
  · exact iff_of_true (hr.monotone h) ((strictMono_rankWith _).monotone h)
  · rcases h.eq_or_lt with rfl | h
    · simp
    · exact iff_of_false (hr h).not_ge (strictMono_rankWith _ h).not_ge

/-- The class of the hierarchy of obstruents, nasals, liquids, glides and vowels that a class
falls in, with /h/ among the obstruents. -/
def toSonority : Class → Sonority
  | obstruent _ | h => .obstruent
  | nasal => .nasal
  | trill | flap | lateral | rhotic => .liquid
  | glide => .glide
  | highCentral | schwa | high | mid | low => .vowel

/-- The hierarchy of obstruents, nasals, liquids, glides and vowels coarsens Table 5.28, however
the voiceless fricatives and the voiced stops are ranked (p. 241). -/
theorem coarsens_toSonority (o : Ordering) : Sonority.Coarsens toSonority (rankWith o) := by
  revert o
  unfold Sonority.Coarsens
  decide +kernel

theorem monotone_toSonority : Monotone toSonority := fun a b h ↦ coarsens_toSonority .lt a b h.1

/-- `toSonority` as an order homomorphism. -/
@[simps]
def toSonorityHom : Class →o Sonority := ⟨toSonority, monotone_toSonority⟩

-- p. 240: a language conflates the scale by collapsing adjacent ranks
theorem contiguous_toSonority (o : Ordering) (c : Sonority) :
    Sonority.Contiguous (rankWith o) (toSonority ⁻¹' {c}) :=
  .of_coarsens (coarsens_toSonority o) ⟨{c}, Set.ordConnected_singleton, rfl⟩

end Class

/-! ### Contiguity -/

open Sonority

-- p. 68: the two orders yield four natural classes
example (v : Bool) :
    IsNaturalClass (Finset.univ.image column)
        ((Finset.univ.filter (·.continuant = v)).image column) ∧
      IsNaturalClass (Finset.univ.image column)
        ((Finset.univ.filter (·.voice = v)).image column) := by
  revert v
  decide +kernel

variable {α : Type*} [LinearOrder α] {r : Obstruent → α}

/-- On a strictly monotone ranking, the classes of [continuant] are contiguous exactly when the
voiceless fricatives outrank the voiced stops, as in (3.6a). -/
theorem contiguous_continuant_iff (hr : StrictMono r) :
    (∀ v, Contiguous r {o | o.continuant = v}) ↔ r voicedStop < r voicelessFricative := by
  have key : ∀ o : Ordering,
      (∀ v, Contiguous (hierarchy o) {x | x.continuant = v}) ↔ o = .gt := by decide +kernel
  exact (forall_congr' fun _ ↦ contiguous_congr (le_iff_hierarchy_le hr)).trans
    ((key _).trans compare_gt_iff_gt)

-- (3.6b)
theorem contiguous_voice_iff (hr : StrictMono r) :
    (∀ v, Contiguous r {o | o.voice = v}) ↔ r voicelessFricative < r voicedStop := by
  have key : ∀ o : Ordering,
      (∀ v, Contiguous (hierarchy o) {x | x.voice = v}) ↔ o = .lt := by decide +kernel
  exact (forall_congr' fun _ ↦ contiguous_congr (le_iff_hierarchy_le hr)).trans
    ((key _).trans compare_lt_iff_lt)

/-- No ranking divides the obstruents into contiguous classes of both [continuant] and [voice]. -/
theorem not_contiguous_continuant_and_voice (r : Obstruent → α) :
    ¬ ((∀ v, Contiguous r {o | o.continuant = v}) ∧ ∀ v, Contiguous r {o | o.voice = v}) :=
  not_contiguous_of_independent r fun x y ↦ ⟨⟨x, y⟩, rfl, rfl⟩

end Parker2002
