module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Order.Closure
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.UpperLower.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Prod

/-!
# Order-connected sets and contiguous maps

This file shows that an order-connected finset containing `⊤` is an interval `Icc a ⊤`, and
defines contiguous maps, maps whose fibres are order-connected. Over a linear order with finite
lower intervals, a map is contiguous iff some monotone map to `ℕ` has the same kernel.

`[UPSTREAM]` candidate for `Mathlib/Order/Interval/Set/OrdConnected.lean` and
`Mathlib/Order/Interval/Finset/Basic.lean`.

## Main definitions

* `Set.ordConnectedHull`: the least order-connected set containing a set, as a closure operator.
* `IsContiguous`: a map whose fibres are order-connected.
* `Set.OrdConnectedAlong`: a set that is the preimage under a map of an order-connected set.

## Main statements

* `isContiguous_iff_ordConnected_preimage`: contiguity in terms of fibres.
* `Monotone.isContiguous`: monotone maps are contiguous.
* `List.isContiguous_get_replicate_append`, `List.isContiguous_get_flatMap_replicate`: contiguity
  of a list built from blocks.
* `isContiguous_iff_exists_monotone`: contiguous maps are those with the kernel of a monotone map
  to `ℕ`.
* `Finset.eq_Icc_top_of_ordConnected_coe`: an order-connected finset containing `⊤` is
  `Icc a ⊤`.
* `Set.OrdConnected.isUpperSet_of_top_mem`: an order-connected set containing `⊤` is an upper
  set.
* `isLowerSet_iff_ordConnected_and_bot_mem`: the nonempty lower sets are the order-connected
  sets containing `⊥`.
* `Set.not_ordConnectedAlong_of_surjective`: two Boolean maps whose values combine freely do
  not both have fibres order-connected along a map to a linear order.
-/

@[expose] public section

/-- The order-connected hull of a set is the least order-connected set containing it. -/
def Set.ordConnectedHull {α : Type*} [Preorder α] : ClosureOperator (Set α) :=
  .ofCompletePred Set.OrdConnected fun _ ↦ Set.ordConnected_sInter

theorem Set.ordConnected_ordConnectedHull {α : Type*} [Preorder α] (s : Set α) :
    (Set.ordConnectedHull s).OrdConnected :=
  Set.ordConnectedHull.isClosed_closure s

/-- A point is in the hull of `s` when it lies between two points of `s`. -/
theorem Set.mem_ordConnectedHull {α : Type*} [Preorder α] {s : Set α} {a : α} :
    a ∈ Set.ordConnectedHull s ↔ ∃ x ∈ s, ∃ y ∈ s, x ≤ a ∧ a ≤ y := by
  refine ⟨fun h ↦ ?_, fun ⟨x, hx, y, hy, hxa, hay⟩ ↦ ?_⟩
  · have hc : Set.ordConnectedHull.IsClosed {a | ∃ x ∈ s, ∃ y ∈ s, x ≤ a ∧ a ≤ y} :=
      ⟨fun a ⟨x, hx, _, _, hxa, _⟩ b ⟨_, _, y, hy, _, hby⟩ c hc ↦
        ⟨x, hx, y, hy, hxa.trans hc.1, hc.2.trans hby⟩⟩
    exact ClosureOperator.closure_min (fun a ha ↦ ⟨a, ha, a, ha, le_rfl, le_rfl⟩) hc h
  · exact (s.ordConnected_ordConnectedHull).out (Set.ordConnectedHull.le_closure s hx)
      (Set.ordConnectedHull.le_closure s hy) ⟨hxa, hay⟩

theorem Set.ordConnectedHull_eq_self_iff {α : Type*} [Preorder α] {s : Set α} :
    Set.ordConnectedHull s = s ↔ s.OrdConnected :=
  Set.ordConnectedHull.isClosed_iff.symm

/-- An order-connected set containing the top element is an upper set. -/
theorem Set.OrdConnected.isUpperSet_of_top_mem {α : Type*} [Preorder α] [OrderTop α]
    {s : Set α} (hs : s.OrdConnected) (ht : ⊤ ∈ s) : IsUpperSet s :=
  fun _ _ hab ha ↦ hs.out ha ht ⟨hab, le_top⟩

/-- A nonempty set is a lower set exactly when it is order-connected and contains the bottom
element. -/
theorem isLowerSet_iff_ordConnected_and_bot_mem {α : Type*} [Preorder α] [OrderBot α]
    {s : Set α} (hne : s.Nonempty) : IsLowerSet s ↔ s.OrdConnected ∧ ⊥ ∈ s :=
  ⟨fun h ↦ ⟨h.ordConnected, h bot_le hne.some_mem⟩,
    fun ⟨hc, hb⟩ _ _ hba ha ↦ hc.out hb ha ⟨bot_le, hba⟩⟩

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

/-- A map `p` is contiguous if `p i = p k` implies `p i = p j` whenever `i ≤ j ≤ k`. -/
def IsContiguous (p : ι → F) : Prop :=
  ∀ ⦃i j k : ι⦄, i ≤ j → j ≤ k → p i = p k → p i = p j

instance [Fintype ι] [DecidableLE ι] [DecidableEq F] (p : ι → F) :
    Decidable (IsContiguous p) :=
  inferInstanceAs (Decidable (∀ i j k : ι, i ≤ j → j ≤ k → p i = p k → p i = p j))

/-- A map is contiguous iff its fibres are order-connected. -/
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

theorem isContiguous_comp_iff {G : Type*} {h : F → G} (hh : Function.Injective h) {p : ι → F} :
    IsContiguous (h ∘ p) ↔ IsContiguous p :=
  ⟨fun hp _ _ _ hij hjk he ↦ hh (hp hij hjk (congrArg h he)),
    fun hp _ _ _ hij hjk he ↦ congrArg h (hp hij hjk (hh he))⟩

theorem IsContiguous.comp_monotone {κ : Type*} [Preorder κ] {p : ι → F} (hp : IsContiguous p)
    {f : κ → ι} (hf : Monotone f) : IsContiguous (p ∘ f) :=
  fun _ _ _ hij hjk heq ↦ hp (hf hij) (hf hjk) heq

theorem IsContiguous.comp_antitone {κ : Type*} [Preorder κ] {p : ι → F} (hp : IsContiguous p)
    {f : κ → ι} (hf : Antitone f) : IsContiguous (p ∘ f) :=
  fun _ _ _ hij hjk heq ↦ heq.trans (hp (hf hjk) (hf hij) heq.symm)

end Preorder

section LinearOrder

variable {ι F : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] {p : ι → F} {i j : ι}

/-- The number of values `p` takes on `Iic i`. -/
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

/-- Over a linear order with finite lower intervals, a map is contiguous iff some monotone map to
`ℕ` has the same kernel. -/
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

/-- A block of copies of `a` before a contiguous list that does not contain `a` is contiguous. -/
theorem List.isContiguous_get_replicate_append {α : Type*} {a : α} {L : List α} (n : ℕ)
    (hL : IsContiguous L.get) (ha : a ∉ L) : IsContiguous (List.replicate n a ++ L).get := by
  intro i j k hij hjk h
  have hi := i.2; have hj := j.2; have hk := k.2
  simp only [List.length_append, List.length_replicate] at hi hj hk
  simp only [List.get_eq_getElem, List.getElem_append, List.length_replicate,
    List.getElem_replicate] at h ⊢
  have hij' : i.1 ≤ j.1 := hij
  have hjk' : j.1 ≤ k.1 := hjk
  by_cases h1 : i.1 < n
  · by_cases h3 : k.1 < n
    · simp only [h1, show j.1 < n by omega, ↓reduceDIte]
    · simp only [h1, h3, ↓reduceDIte] at h
      exact absurd (h ▸ List.getElem_mem _) ha
  · simp only [h1, show ¬ k.1 < n by omega, ↓reduceDIte] at h
    simp only [h1, show ¬ j.1 < n by omega, ↓reduceDIte]
    exact @hL ⟨i - n, by omega⟩ ⟨j - n, by omega⟩ ⟨k - n, by omega⟩
      (by simp [Fin.le_def]; omega) (by simp [Fin.le_def]; omega) h

/-- Blocks of copies of distinct elements, one after another, form a contiguous list. -/
theorem List.isContiguous_get_flatMap_replicate {α : Type*} {l : List (ℕ × α)}
    (h : (l.map Prod.snd).Nodup) :
    IsContiguous (l.flatMap fun p ↦ List.replicate p.1 p.2).get := by
  induction l with
  | nil => exact fun i ↦ i.elim0
  | cons p l ih =>
    rw [List.map_cons, List.nodup_cons] at h
    refine List.isContiguous_get_replicate_append _ (ih h.2) fun hm ↦ h.1 ?_
    obtain ⟨q, hq, hpq⟩ := List.mem_flatMap.mp hm
    exact (List.eq_of_mem_replicate hpq) ▸ List.mem_map_of_mem hq

/-! ### Sets order-connected along a map -/

namespace Set

variable {α β γ : Type*} {S : Set α}

section Preorder

variable [Preorder β] [Preorder γ] {f : α → β} {g : α → γ}

/-- A set is order-connected along `f` when it is the preimage under `f` of an order-connected
set. -/
def OrdConnectedAlong (S : Set α) (f : α → β) : Prop := ∃ I : Set β, I.OrdConnected ∧ S = f ⁻¹' I

theorem ordConnectedAlong_iff :
    S.OrdConnectedAlong f ↔ ∀ a ∈ S, ∀ b ∈ S, ∀ c, f a ≤ f c → f c ≤ f b → c ∈ S := by
  refine ⟨?_, fun h ↦ ⟨{x | ∃ a ∈ S, ∃ b ∈ S, f a ≤ x ∧ x ≤ f b}, ⟨?_⟩, ?_⟩⟩
  · rintro ⟨I, hI, rfl⟩ a ha b hb c hac hcb
    exact hI.out ha hb ⟨hac, hcb⟩
  · rintro x ⟨a, ha, -, -, hax, -⟩ y ⟨-, -, b, hb, -, hyb⟩ z ⟨hxz, hzy⟩
    exact ⟨a, ha, b, hb, hax.trans hxz, hzy.trans hyb⟩
  · ext c
    exact ⟨fun hc ↦ ⟨c, hc, c, hc, le_rfl, le_rfl⟩,
      fun ⟨a, ha, b, hb, hac, hcb⟩ ↦ h a ha b hb c hac hcb⟩

instance [Fintype α] [DecidableLE β] [DecidablePred (· ∈ S)] :
    Decidable (S.OrdConnectedAlong f) :=
  decidable_of_iff _ ordConnectedAlong_iff.symm

@[simp] theorem ordConnectedAlong_id {S : Set β} : S.OrdConnectedAlong id ↔ S.OrdConnected :=
  ⟨fun ⟨_, hI, h⟩ ↦ h ▸ hI, fun h ↦ ⟨S, h, rfl⟩⟩

/-- A set order-connected along `g` is order-connected along any `f` whose order `g` preserves. -/
theorem OrdConnectedAlong.of_le_imp_le (h : ∀ a b, f a ≤ f b → g a ≤ g b)
    (hS : S.OrdConnectedAlong g) : S.OrdConnectedAlong f :=
  ordConnectedAlong_iff.2 fun a ha b hb c hac hcb ↦
    ordConnectedAlong_iff.1 hS a ha b hb c (h a c hac) (h c b hcb)

/-- Maps that induce the same order have the same order-connected sets along them. -/
theorem ordConnectedAlong_congr (h : ∀ a b, f a ≤ f b ↔ g a ≤ g b) :
    S.OrdConnectedAlong f ↔ S.OrdConnectedAlong g := by
  simp only [ordConnectedAlong_iff, h]

end Preorder

/-- Two Boolean maps whose values combine freely do not both have fibres order-connected along a
map to a linear order. -/
theorem not_ordConnectedAlong_of_surjective [LinearOrder β] (f : α → β) {φ ψ : α → Bool}
    (h : Function.Surjective fun a ↦ (φ a, ψ a)) :
    ¬ ((∀ v, {a | φ a = v}.OrdConnectedAlong f) ∧ ∀ v, {a | ψ a = v}.OrdConnectedAlong f) := by
  rintro ⟨hφ, hψ⟩
  -- the lower of the two neighbours of a least combination lies between it and the other
  have h' : ∀ x y, ∃ a, φ a = x ∧ ψ a = y := fun x y ↦
    (h (x, y)).imp fun a ha ↦ ⟨congrArg Prod.fst ha, congrArg Prod.snd ha⟩
  choose w hw using h'
  obtain ⟨⟨x, y⟩, hm⟩ := Finite.exists_min fun p : Bool × Bool ↦ f (w p.1 p.2)
  rcases le_total (f (w (!x) y)) (f (w x (!y))) with hle | hle
  · have := ordConnectedAlong_iff.1 (hφ x) (w x y) (hw x y).1 (w x (!y)) (hw x (!y)).1 (w (!x) y)
      (hm (!x, y)) hle
    simp [(hw (!x) y).1] at this
  · have := ordConnectedAlong_iff.1 (hψ y) (w x y) (hw x y).2 (w (!x) y) (hw (!x) y).2 (w x (!y))
      (hm (x, !y)) hle
    simp [(hw x (!y)).2] at this

end Set
