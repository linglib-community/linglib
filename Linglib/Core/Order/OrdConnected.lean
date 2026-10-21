module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Order-connected sets and contiguous maps

`[UPSTREAM]` candidate for `Mathlib/Order/Interval/Set/OrdConnected.lean` and
`Mathlib/Order/Interval/Finset/Basic.lean`. A map is contiguous when its fibres are
order-connected, so that no value recurs across a distinct intervening value; over a linear order
with finite lower intervals these are exactly the maps with the kernel of a monotone map to `ℕ`. This is the shape of a
contiguous segment of a hierarchy wherever a linguistic scale is linearly ordered and a strategy
covers a run of it.

## Main definitions

* `IsContiguous`: no value recurs across a distinct intervening value.

## Main statements

* `isContiguous_iff_ordConnected_preimage`: contiguity is order-connectedness of every fibre.
* `Monotone.isContiguous`: a monotone map is contiguous.
* `isContiguous_iff_exists_monotone`: over a linear order with finite lower intervals, a map is
  contiguous exactly when some monotone map to `ℕ` has its kernel.
* `Finset.eq_Icc_top_of_ordConnected_coe`: with the top element in the set, the interval
  reaches it.
* `Set.OrdConnected.isUpperSet_of_top_mem`: an order-connected set containing the top element
  is an upper set.
-/

@[expose] public section

/-- An order-connected set containing the top element is an upper set. -/
theorem Set.OrdConnected.isUpperSet_of_top_mem {α : Type*} [Preorder α] [OrderTop α]
    {s : Set α} (hs : s.OrdConnected) (ht : ⊤ ∈ s) : IsUpperSet s :=
  fun _ _ hab ha ↦ hs.out ha ht ⟨hab, le_top⟩

namespace Finset

variable {α : Type*}

/-- Order-connectedness of a finset is decided on its closed intervals. -/
instance decidableOrdConnectedCoe [Preorder α] [DecidableEq α] [LocallyFiniteOrder α]
    (s : Finset α) : Decidable (s : Set α).OrdConnected :=
  decidable_of_iff (∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ Icc x y, z ∈ s) <| by
    simp only [Set.ordConnected_iff, Set.subset_def, Set.mem_Icc, mem_coe, mem_Icc, and_imp]
    exact ⟨fun h x hx y hy _ z hxz hzy ↦ h x hx y hy z hxz hzy,
      fun h x hx y hy z hxz hzy ↦ h x hx y hy (hxz.trans hzy) z hxz hzy⟩

variable [LinearOrder α] [LocallyFiniteOrder α] {s : Finset α}

/-- An order-connected finset containing the top element is the closed interval from its least
element up to the top. -/
theorem eq_Icc_top_of_ordConnected_coe [OrderTop α] (hc : (s : Set α).OrdConnected) (ht : ⊤ ∈ s) :
    s = Icc (s.min' ⟨⊤, ht⟩) ⊤ := by
  ext p
  simp only [mem_Icc, le_top, and_true]
  exact ⟨min'_le _ _, fun h ↦ hc.out (min'_mem _ _) ht ⟨h, le_top⟩⟩

end Finset

/-! ### Contiguous maps -/

section Preorder

variable {ι F : Type*} [Preorder ι]

/-- A map is **contiguous** when no value recurs across a distinct intervening value: if the
values at `i ≤ k` agree, every value between them agrees too. -/
def IsContiguous (p : ι → F) : Prop :=
  ∀ ⦃i j k : ι⦄, i ≤ j → j ≤ k → p i = p k → p i = p j

instance [Fintype ι] [DecidableLE ι] [DecidableEq F] (p : ι → F) :
    Decidable (IsContiguous p) :=
  inferInstanceAs (Decidable (∀ i j k : ι, i ≤ j → j ≤ k → p i = p k → p i = p j))

/-- Contiguity is order-connectedness of every fibre. -/
theorem isContiguous_iff_ordConnected_preimage (p : ι → F) :
    IsContiguous p ↔ ∀ y, (p ⁻¹' {y}).OrdConnected := by
  refine ⟨fun hp y ↦ ⟨fun i hi k hk j hj ↦ ?_⟩, fun h i j k hij hjk hik ↦ ?_⟩
  · simp only [Set.mem_preimage, Set.mem_singleton_iff] at hi hk ⊢
    exact (hp hj.1 hj.2 (hi.trans hk.symm)).symm.trans hi
  · exact ((h (p i)).out (Set.mem_singleton _) hik.symm ⟨hij, hjk⟩).symm

/-- A monotone map into a partial order is contiguous. -/
theorem Monotone.isContiguous [PartialOrder F] {f : ι → F} (hf : Monotone f) :
    IsContiguous f :=
  fun _ _ _ hij hjk he ↦ le_antisymm (hf hij) ((hf hjk).trans_eq he.symm)

/-- Postcomposition with an injective map preserves and reflects contiguity. -/
theorem isContiguous_comp_iff {G : Type*} {h : F → G} (hh : Function.Injective h) {p : ι → F} :
    IsContiguous (h ∘ p) ↔ IsContiguous p :=
  ⟨fun hp _ _ _ hij hjk he ↦ hh (hp hij hjk (congrArg h he)),
    fun hp _ _ _ hij hjk he ↦ congrArg h (hp hij hjk (hh he))⟩

/-- Precomposition with a monotone map preserves contiguity. -/
theorem IsContiguous.comp_monotone {κ : Type*} [Preorder κ] {p : ι → F} (hp : IsContiguous p)
    {f : κ → ι} (hf : Monotone f) : IsContiguous (p ∘ f) :=
  fun _ _ _ hij hjk heq ↦ hp (hf hij) (hf hjk) heq

end Preorder

section LinearOrder

variable {ι F : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] {p : ι → F} {i j : ι}

/-- The number of distinct values a map takes up to and including `i`. -/
private def score [DecidableEq F] (p : ι → F) (i : ι) : ℕ := ((Finset.Iic i).image p).card

private theorem score_mono [DecidableEq F] : Monotone (score p) :=
  fun _ _ hij ↦ Finset.card_le_card (Finset.image_subset_image (Finset.Iic_subset_Iic.mpr hij))

private theorem score_eq_of_eq [DecidableEq F] (hp : IsContiguous p) (hij : i ≤ j)
    (hpij : p i = p j) : score p i = score p j := by
  unfold score
  congr 1
  refine Finset.Subset.antisymm
    (Finset.image_subset_image (Finset.Iic_subset_Iic.mpr hij)) (fun x hx ↦ ?_)
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_Iic] at hl
  rcases le_total l i with hli | hil
  · exact Finset.mem_image_of_mem p (Finset.mem_Iic.mpr hli)
  · rw [← hp hil hl hpij]
    exact Finset.mem_image_of_mem p (Finset.mem_Iic.mpr le_rfl)

private theorem eq_of_score_eq [DecidableEq F] (hp : IsContiguous p) (hij : i ≤ j)
    (hs : score p i = score p j) : p i = p j := by
  have heq : (Finset.Iic i).image p = (Finset.Iic j).image p :=
    Finset.eq_of_subset_of_card_le
      (Finset.image_subset_image (Finset.Iic_subset_Iic.mpr hij)) (le_of_eq hs.symm)
  have hj : p j ∈ (Finset.Iic i).image p :=
    heq ▸ Finset.mem_image_of_mem p (Finset.mem_Iic.mpr le_rfl)
  obtain ⟨l, hl, hpl⟩ := Finset.mem_image.mp hj
  rw [Finset.mem_Iic] at hl
  exact (hp hl hij hpl).symm.trans hpl

/-- Over a linear order with finite lower intervals a map is contiguous exactly when some
monotone map to `ℕ` has its kernel. Forward, the number of distinct values up to a point is such a map; backward, the
kernel of a monotone map has order-connected classes. -/
theorem isContiguous_iff_exists_monotone (p : ι → F) :
    IsContiguous p ↔ ∃ g : ι → ℕ, Monotone g ∧ ∀ i j, p i = p j ↔ g i = g j := by
  classical
  refine ⟨fun hp ↦ ⟨score p, score_mono, fun i j ↦ ⟨fun hpij ↦ ?_, fun hs ↦ ?_⟩⟩, ?_⟩
  · rcases le_total i j with h | h
    exacts [score_eq_of_eq hp h hpij, (score_eq_of_eq hp h hpij.symm).symm]
  · rcases le_total i j with h | h
    exacts [eq_of_score_eq hp h hs, (eq_of_score_eq hp h hs.symm).symm]
  · rintro ⟨g, hg, hker⟩ i j k hij hjk heq
    exact (hker i j).mpr (hg.isContiguous hij hjk ((hker i k).mp heq))

end LinearOrder
