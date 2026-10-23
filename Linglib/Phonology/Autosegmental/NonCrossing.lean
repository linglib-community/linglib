/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Basic.Rel
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Preorder.Chain
public import Linglib.Core.Order.Monotone.Monovary

/-!
# Non-crossing association relations

An association line joins position `k` of an upper tier to position `i` of a lower tier, so the
lines between two tiers form a relation `R : SetRel ι κ`. The relation is non-crossing when
`k₁ < k₂` forces `i₁ ≤ i₂` for any two of its lines: its coordinates monovary. Drawn between two
rows, such lines never cross; this is the No-Crossing Constraint of autosegmental phonology,
which Sagey derives from reading association as overlap in time. On linear tiers it says that
the lines are totally ordered componentwise, the order on edges in Yli-Jyrä's definition of an
autosegmental graph.

The window of an upper position `m` is the set of lower positions at or after every position
linked from the left of `m` and at or before every position linked from its right. A line from
`m` can be added without crossing exactly when it ends in the window, and for finitely many
lines on a linear lower tier the nearest position linked on either side lies in the window.

## Main definitions

* `IsNonCrossing R`: no two lines of `R` cross.
* `window R m`: the lower positions that `m` can link to without crossing.
* `leftBound links m`, `rightBound links m`: the nearest positions linked from either side.

## Main results

* `isNonCrossing_iff_isChain`: on linear tiers, a relation is non-crossing iff it is a chain in
  the componentwise order.
* `isNonCrossing_insert_iff_mem_window`: a line can be added iff it ends in its node's window.
* `IsNonCrossing.union_of_leftBound`, `IsNonCrossing.union_of_rightBound`: lines to the nearest
  linked position on one side cross nothing.

## Implementation notes

A finite set of lines `links : Finset (ι × κ)` enters as `(links : SetRel ι κ)`, and
`IsNonCrossing` and window membership are decidable there.

## References

* [goldsmith-1976]
* [sagey-1986]
* [sagey-1988]
* [yli-jyra-2015]
-/

@[expose] public section

namespace Autosegmental

open Set

variable {ι ι' κ κ' : Type*}

/-! ### Non-crossing relations -/

section Preorder
variable [Preorder ι] [Preorder κ] {R S : SetRel ι κ} {p : ι × κ}

/-- A relation between two tiers is non-crossing when its lower coordinate monovaries with its
upper one. -/
def IsNonCrossing (R : SetRel ι κ) : Prop := MonovaryOn Prod.snd Prod.fst R

theorem isNonCrossing_iff :
    IsNonCrossing R ↔ ∀ l₁ ∈ R, ∀ l₂ ∈ R, l₁.1 < l₂.1 → l₁.2 ≤ l₂.2 := Iff.rfl

@[simp] theorem isNonCrossing_empty : IsNonCrossing (∅ : SetRel ι κ) := MonovaryOn.empty

@[simp] theorem isNonCrossing_singleton (p : ι × κ) : IsNonCrossing ({p} : SetRel ι κ) :=
  monovaryOn_singleton p

theorem IsNonCrossing.subset (hRS : R ⊆ S) (h : IsNonCrossing S) : IsNonCrossing R :=
  MonovaryOn.subset hRS h

theorem isNonCrossing_insert_iff :
    IsNonCrossing (insert p R) ↔ IsNonCrossing R ∧
      ∀ q ∈ R, (p.1 < q.1 → p.2 ≤ q.2) ∧ (q.1 < p.1 → q.2 ≤ p.2) :=
  monovaryOn_insert

theorem isNonCrossing_union_iff :
    IsNonCrossing (R ∪ S) ↔ IsNonCrossing R ∧ IsNonCrossing S ∧
      ∀ a ∈ R, ∀ b ∈ S, (a.1 < b.1 → a.2 ≤ b.2) ∧ (b.1 < a.1 → b.2 ≤ a.2) :=
  monovaryOn_union

instance [DecidableLT ι] [DecidableLE κ] (links : Finset (ι × κ)) :
    Decidable (IsNonCrossing (links : SetRel ι κ)) :=
  inferInstanceAs (Decidable (MonovaryOn _ _ (links : Set (ι × κ))))

instance [Fintype ι] [Fintype κ] [DecidableLT ι] [DecidableLE κ] (R : SetRel ι κ)
    [DecidablePred (· ∈ R)] : Decidable (IsNonCrossing R) :=
  decidable_of_iff (∀ a, a ∈ R → ∀ b, b ∈ R → a.1 < b.1 → a.2 ≤ b.2) Iff.rfl

end Preorder

theorem isNonCrossing_image [Preorder ι] [Preorder κ] {R : SetRel ι' κ'}
    (f : ι' × κ' → ι × κ) :
    IsNonCrossing (f '' R) ↔ MonovaryOn (Prod.snd ∘ f) (Prod.fst ∘ f) R :=
  monovaryOn_image f R

section LinearOrder
variable [LinearOrder ι] [LinearOrder κ] {R : SetRel ι κ}

/-- On linear tiers, a relation is non-crossing iff it is a chain in the componentwise order. -/
theorem isNonCrossing_iff_isChain : IsNonCrossing R ↔ IsChain (· ≤ ·) R := by
  refine ⟨fun h a ha b hb _ ↦ ?_, fun h a ha b hb hab ↦ ?_⟩
  · rcases lt_trichotomy a.1 b.1 with hab | hab | hab
    · exact .inl ⟨hab.le, h ha hb hab⟩
    · exact (le_total a.2 b.2).imp (⟨hab.le, ·⟩) (⟨hab.ge, ·⟩)
    · exact .inr ⟨hab.le, h hb ha hab⟩
  · exact ((h ha hb fun h ↦ hab.ne (congrArg Prod.fst h)).resolve_right
      fun hba ↦ hba.1.not_gt hab).2

@[simp] theorem isNonCrossing_inv : IsNonCrossing R.inv ↔ IsNonCrossing R := by
  rw [IsNonCrossing, SetRel.inv, ← image_swap_eq_preimage_swap, monovaryOn_image]
  exact monovaryOn_comm

end LinearOrder

/-! ### The window of a node -/

section Window
variable [Preorder ι] [Preorder κ] {R : SetRel ι κ} {m : ι} {j x y : κ}

variable (R m) in
/-- The window of `m` holds the lower positions at or after every position linked from the left
of `m` and at or before every position linked from its right. -/
def window : Set κ := upperBounds (R.image (Iio m)) ∩ lowerBounds (R.image (Ioi m))

theorem mem_window_iff :
    j ∈ window R m ↔ ∀ p ∈ R, (p.1 < m → p.2 ≤ j) ∧ (m < p.1 → j ≤ p.2) := by
  simp only [window, mem_inter_iff, mem_upperBounds, mem_lowerBounds, SetRel.mem_image,
    mem_Iio, mem_Ioi, Prod.forall]
  grind

instance [DecidableLT ι] [DecidableLE κ] (links : Finset (ι × κ)) (m : ι) :
    DecidablePred (· ∈ window (links : SetRel ι κ) m) := fun _ ↦
  decidable_of_iff (∀ p ∈ links, (p.1 < m → p.2 ≤ _) ∧ (m < p.1 → _ ≤ p.2))
    mem_window_iff.symm

theorem notMem_window_of_mem_image_Iio (hx : x ∈ R.image (Iio m)) (h : j < x) :
    j ∉ window R m := fun hj ↦ (hj.1 hx).not_gt h

theorem notMem_window_of_mem_image_Ioi (hx : x ∈ R.image (Ioi m)) (h : x < j) :
    j ∉ window R m := fun hj ↦ (hj.2 hx).not_gt h

/-- A line can be added iff it ends in its node's window. -/
theorem isNonCrossing_insert_iff_mem_window :
    IsNonCrossing (insert (m, j) R) ↔ IsNonCrossing R ∧ j ∈ window R m := by
  rw [isNonCrossing_insert_iff, mem_window_iff]
  exact and_congr_right' <| forall₂_congr fun _ _ ↦ and_comm

theorem IsNonCrossing.insert_of_mem_window (h : IsNonCrossing R) (hj : j ∈ window R m) :
    IsNonCrossing (insert (m, j) R) :=
  isNonCrossing_insert_iff_mem_window.2 ⟨h, hj⟩

theorem IsNonCrossing.le_of_mem_image (h : IsNonCrossing R) (hx : x ∈ R.image (Iio m))
    (hy : y ∈ R.image (Ioi m)) : x ≤ y := by
  obtain ⟨n, hn, hx⟩ := hx
  obtain ⟨n', hn', hy⟩ := hy
  exact h hx hy (lt_trans hn hn')

end Window

/-! ### The endpoints of the window -/

section Bound
variable [Preorder ι] [DecidableLT ι] [LinearOrder κ] (links : Finset (ι × κ)) (m : ι)

/-- The lower positions linked from upper positions left of `m`. -/
def leftIndices : Finset κ := (links.filter (·.1 < m)).image (·.2)

/-- The lower positions linked from upper positions right of `m`. -/
def rightIndices : Finset κ := (links.filter (m < ·.1)).image (·.2)

/-- The nearest lower position linked from an upper position left of `m`. -/
def leftBound : WithBot κ := (leftIndices links m).max

/-- The nearest lower position linked from an upper position right of `m`. -/
def rightBound : WithTop κ := (rightIndices links m).min

variable {links m} {j x : κ}

@[simp] theorem mem_leftIndices : x ∈ leftIndices links m ↔ ∃ n < m, (n, x) ∈ links := by
  simp [leftIndices, Prod.exists, and_comm]

@[simp] theorem mem_rightIndices :
    x ∈ rightIndices links m ↔ ∃ n, m < n ∧ (n, x) ∈ links := by
  simp [rightIndices, Prod.exists, and_comm]

@[norm_cast] theorem coe_leftIndices :
    (leftIndices links m : Set κ) = SetRel.image (links : SetRel ι κ) (Iio m) := by
  ext; simp

@[norm_cast] theorem coe_rightIndices :
    (rightIndices links m : Set κ) = SetRel.image (links : SetRel ι κ) (Ioi m) := by
  ext; simp

theorem leftIndices_mono : Monotone (leftIndices links) := by
  intro _ _ hm x hx
  obtain ⟨n, hn, hx⟩ := mem_leftIndices.1 hx
  exact mem_leftIndices.2 ⟨n, hn.trans_le hm, hx⟩

theorem rightIndices_anti : Antitone (rightIndices links) := by
  intro _ _ hm x hx
  obtain ⟨n, hn, hx⟩ := mem_rightIndices.1 hx
  exact mem_rightIndices.2 ⟨n, hm.trans_lt hn, hx⟩

theorem leftBound_mono : Monotone (leftBound links) := fun _ _ hm ↦
  Finset.max_mono (leftIndices_mono hm)

theorem rightBound_mono : Monotone (rightBound links) := fun _ _ hm ↦
  Finset.min_mono (rightIndices_anti hm)

theorem IsNonCrossing.mem_window_of_leftBound_eq (h : IsNonCrossing (links : SetRel ι κ))
    (hj : leftBound links m = j) : j ∈ window (links : SetRel ι κ) m := by
  refine ⟨fun x hx ↦ Finset.le_max_of_eq ?_ hj, fun _ hy ↦ h.le_of_mem_image ?_ hy⟩
  · rwa [← Finset.mem_coe, coe_leftIndices]
  · rw [← coe_leftIndices]; exact Finset.mem_of_max hj

theorem IsNonCrossing.mem_window_of_rightBound_eq (h : IsNonCrossing (links : SetRel ι κ))
    (hj : rightBound links m = j) : j ∈ window (links : SetRel ι κ) m := by
  refine ⟨fun _ hx ↦ h.le_of_mem_image hx ?_, fun y hy ↦ Finset.min_le_of_eq ?_ hj⟩
  · rw [← coe_rightIndices]; exact Finset.mem_of_min hj
  · rwa [← Finset.mem_coe, coe_rightIndices]

/-- Lines from any nodes to the nearest position linked left of each cross neither one another
nor the lines of a non-crossing set, so spreading to the left never crosses. -/
theorem IsNonCrossing.union_of_leftBound [DecidableEq ι] (h : IsNonCrossing (links : SetRel ι κ))
    {s : Finset (ι × κ)} (hs : ∀ p ∈ s, leftBound links p.1 = p.2) :
    IsNonCrossing ((links ∪ s : Finset (ι × κ)) : SetRel ι κ) := by
  rw [Finset.coe_union]
  refine isNonCrossing_union_iff.2 ⟨h, fun p hp q hq hpq ↦ ?_,
    fun a ha b hb ↦ mem_window_iff.1 (h.mem_window_of_leftBound_eq (hs b hb)) a ha⟩
  exact WithBot.coe_le_coe.1
    ((hs p hp).symm.trans_le ((leftBound_mono hpq.le).trans_eq (hs q hq)))

/-- Lines from any nodes to the nearest position linked right of each cross neither one another
nor the lines of a non-crossing set, so spreading to the right never crosses. -/
theorem IsNonCrossing.union_of_rightBound [DecidableEq ι]
    (h : IsNonCrossing (links : SetRel ι κ)) {s : Finset (ι × κ)}
    (hs : ∀ p ∈ s, rightBound links p.1 = p.2) :
    IsNonCrossing ((links ∪ s : Finset (ι × κ)) : SetRel ι κ) := by
  rw [Finset.coe_union]
  refine isNonCrossing_union_iff.2 ⟨h, fun p hp q hq hpq ↦ ?_,
    fun a ha b hb ↦ mem_window_iff.1 (h.mem_window_of_rightBound_eq (hs b hb)) a ha⟩
  exact WithTop.coe_le_coe.1
    ((hs p hp).symm.trans_le ((rightBound_mono hpq.le).trans_eq (hs q hq)))

end Bound

end Autosegmental
