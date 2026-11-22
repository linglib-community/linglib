/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Segmental.Sonority.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic.Order

/-!
# Obstruent classes on a sonority scale

Sonority scales that divide the obstruents rank fricatives above stops and voiced obstruents
above voiceless ones. `Phonology.Sonority.ObstruentClass` is a pair of values of [continuant] and
[voice], and the four classes carry the product order: the two rankings hold, and the voiceless
fricatives and the voiced stops are unordered.

A ranking `r` of the four classes in a linear order that is strictly monotone for the product
order is determined, up to the order it induces, by
`compare (r voicelessFricative) (r voicedStop)`: it induces the order of `ObstruentClass.rank o`
at that value `o` (`le_iff_rank_le`), so there are three such rankings. On such a ranking the
classes of [continuant] are contiguous exactly when the voiceless fricatives outrank the voiced
stops (`ordConnectedAlong_continuant_iff`), and those of [voice] exactly when the voiced stops
outrank the voiceless fricatives (`ordConnectedAlong_voice_iff`); on a tie neither are. On no
ranking at all are both (`not_ordConnectedAlong_continuant_and_voice`). All four results are in
the namespace `Phonology.Sonority.ObstruentClass`.

`Phonology.Sonority.ofSegmentWith o` is the scale on segments that divides the obstruents by
`ObstruentClass.rank o` and leaves the other classes of the hierarchy whole; the hierarchy
coarsens it.

## References

* [parker-2002]
-/

@[expose] public section

namespace Phonology.Sonority

/-- An obstruent class, by its values of [continuant] and [voice]. -/
@[ext]
structure ObstruentClass where
  /-- Whether the class is [+continuant], a class of fricatives. -/
  continuant : Bool
  /-- Whether the class is [+voice]. -/
  voice : Bool
  deriving DecidableEq, Repr, Fintype, Inhabited

namespace ObstruentClass

/-- The voiceless stops and affricates. -/
def voicelessStop : ObstruentClass := ⟨false, false⟩

/-- The voiceless fricatives. -/
def voicelessFricative : ObstruentClass := ⟨true, false⟩

/-- The voiced stops and affricates. -/
def voicedStop : ObstruentClass := ⟨false, true⟩

/-- The voiced fricatives. -/
def voicedFricative : ObstruentClass := ⟨true, true⟩

/-- A class as its pair of values. -/
@[simps]
def equivProd : ObstruentClass ≃ Bool × Bool where
  toFun o := (o.continuant, o.voice)
  invFun p := ⟨p.1, p.2⟩

/-- The product order, which puts fricatives above stops and voiced obstruents above voiceless
ones. -/
instance : PartialOrder ObstruentClass := PartialOrder.lift equivProd equivProd.injective

instance : DecidableLE ObstruentClass := fun a b ↦
  inferInstanceAs (Decidable (a.continuant ≤ b.continuant ∧ a.voice ≤ b.voice))

instance : DecidableLT ObstruentClass := decidableLTOfDecidableLE

/-- `equivProd` as an order isomorphism. -/
@[simps!]
def orderIsoProd : ObstruentClass ≃o Bool × Bool where
  toEquiv := equivProd
  map_rel_iff' := .rfl

/-- The features of a class. -/
def column (o : ObstruentClass) : Segment :=
  (([−sonorant] : Segment).setFeature .continuant o.continuant).setFeature .voice o.voice

/-- The class of a segment, by its values of [continuant] and [voice]. -/
def ofSegment (s : Segment) : ObstruentClass :=
  ⟨decide (s .continuant = true), decide (s .voice = true)⟩

@[simp] theorem ofSegment_column (o : ObstruentClass) : ofSegment o.column = o := by
  revert o
  decide

/-- The four classes are natural classes of their columns. -/
example (v : Bool) :
    IsNaturalClass (Finset.univ.image column)
        ((Finset.univ.filter (·.continuant = v)).image column) ∧
      IsNaturalClass (Finset.univ.image column)
        ((Finset.univ.filter (·.voice = v)).image column) := by
  revert v
  decide +kernel

/-! ### Rankings -/

/-- The ranking of the obstruent classes that compares the voiceless fricatives with the voiced
stops by `o`: below them for `lt`, level with them for `eq`, and above them for `gt`. These are
the three hierarchies of [parker-2002]'s (3.6), (b), (c) and (a) in that order. -/
def rank (o : Ordering) : ObstruentClass → ℕ
  | ⟨false, false⟩ => 1
  | ⟨true, false⟩ => if o = .gt then 3 else 2
  | ⟨false, true⟩ => if o = .lt then 3 else 2
  | ⟨true, true⟩ => 4

theorem strictMono_rank (o : Ordering) : StrictMono (rank o) := by
  revert o
  simp only [StrictMono]
  decide +kernel

@[simp] theorem compare_rank (o : Ordering) :
    compare (rank o voicelessFricative) (rank o voicedStop) = o := by
  cases o <;> rfl

variable {α : Type*} [LinearOrder α] {r : ObstruentClass → α}

/-- A ranking of the obstruent classes strictly monotone for the product order induces the order
of the `rank o` that compares the voiceless fricatives with the voiced stops as it does. -/
theorem le_iff_rank_le (hr : StrictMono r) (x y : ObstruentClass) :
    r x ≤ r y ↔ rank (compare (r voicelessFricative) (r voicedStop)) x ≤
      rank (compare (r voicelessFricative) (r voicedStop)) y := by
  have h₁ : r voicelessStop < r voicelessFricative := hr (by decide)
  have h₂ : r voicelessStop < r voicedStop := hr (by decide)
  have h₃ : r voicelessFricative < r voicedFricative := hr (by decide)
  have h₄ : r voicedStop < r voicedFricative := hr (by decide)
  simp only [voicelessStop, voicelessFricative, voicedStop, voicedFricative] at *
  rcases lt_trichotomy (r ⟨true, false⟩) (r ⟨false, true⟩) with h | h | h <;>
    [rw [compare_lt_iff_lt.2 h]; rw [compare_eq_iff_eq.2 h]; rw [compare_gt_iff_gt.2 h]] <;>
    rcases x with ⟨_ | _, _ | _⟩ <;> rcases y with ⟨_ | _, _ | _⟩ <;> simp [rank] <;> order

/-! ### Contiguity -/

/-- On a strictly monotone ranking, the classes of [continuant] are contiguous exactly when the
voiceless fricatives outrank the voiced stops. -/
theorem ordConnectedAlong_continuant_iff (hr : StrictMono r) :
    (∀ v, {o | o.continuant = v}.OrdConnectedAlong r) ↔ r voicedStop < r voicelessFricative := by
  have key : ∀ o : Ordering,
      (∀ v, {x | x.continuant = v}.OrdConnectedAlong (rank o)) ↔ o = .gt := by decide +kernel
  exact (forall_congr' fun _ ↦ Set.ordConnectedAlong_congr (le_iff_rank_le hr)).trans
    ((key _).trans compare_gt_iff_gt)

/-- On a strictly monotone ranking, the classes of [voice] are contiguous exactly when the voiced
stops outrank the voiceless fricatives. -/
theorem ordConnectedAlong_voice_iff (hr : StrictMono r) :
    (∀ v, {o | o.voice = v}.OrdConnectedAlong r) ↔ r voicelessFricative < r voicedStop := by
  have key : ∀ o : Ordering,
      (∀ v, {x | x.voice = v}.OrdConnectedAlong (rank o)) ↔ o = .lt := by decide +kernel
  exact (forall_congr' fun _ ↦ Set.ordConnectedAlong_congr (le_iff_rank_le hr)).trans
    ((key _).trans compare_lt_iff_lt)

/-- No ranking divides the obstruents into contiguous classes of both [continuant] and [voice]. -/
theorem not_ordConnectedAlong_continuant_and_voice (r : ObstruentClass → α) :
    ¬ ((∀ v, {o | o.continuant = v}.OrdConnectedAlong r) ∧
      ∀ v, {o | o.voice = v}.OrdConnectedAlong r) :=
  Set.not_ordConnectedAlong_of_surjective r equivProd.surjective

end ObstruentClass

/-! ### The scale on segments -/

/-- The sonority of a segment with the obstruents divided: its class in the hierarchy, and within
the obstruents the rank of its class on `ObstruentClass.rank o`. -/
def ofSegmentWith (o : Ordering) (x : Segment) : Sonority ×ₗ ℕ :=
  toLex (ofSegment x, if ofSegment x = .obstruent then ObstruentClass.rank o (.ofSegment x) else 0)

theorem coarsens_ofSegment_ofSegmentWith (o : Ordering) : Coarsens ofSegment (ofSegmentWith o) :=
  fun _ _ h ↦ Prod.Lex.monotone_fst _ _ h

end Phonology.Sonority
