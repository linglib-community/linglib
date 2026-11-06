module

public import Mathlib.Order.SupClosed
public import Mathlib.Data.Finset.Image
public import Mathlib.Order.CompleteLattice.Finset

/-!
# The sup-closure of an indexed family

[UPSTREAM] candidate for `Mathlib/Order/SupClosed.lean`.

The sup-closure of the image of a set of indices is the set of sups of the family over the
nonempty finite sets of those indices, and dually for the inf-closure. For a family of sets
these are the unions and the intersections of its members over nonempty finite sets of indices.
Closing a set under sups does not change its infimum, nor closing it under infs its supremum. A
finite lower set has a greatest element exactly when it is nonempty and sup-closed, so the values
in an upper set of an order-reversing embedding of a finite semilattice have a least element
exactly when the points sent there are sup-closed.

## Main results

* `mem_supClosure_image`, `mem_infClosure_image`: membership in the closure of an image.
* `Set.mem_supClosure_image`, `Set.mem_infClosure_image`: the same for a family of sets.
* `sInf_supClosure`, `sSup_infClosure`: the closures keep the infimum and the supremum.
* `IsLowerSet.exists_isGreatest_iff`: a finite lower set has a greatest element iff it is
  nonempty and sup-closed.
* `exists_isLeast_range_inter_iff`: the same for the least value of an order-reversing embedding.
-/

public section

variable {ι α : Type*}

section SemilatticeSup

variable [SemilatticeSup α] {f : ι → α} {s : Set ι} {a : α}

@[to_dual]
theorem mem_supClosure_image :
    a ∈ supClosure (f '' s) ↔ ∃ (t : Finset ι) (ht : t.Nonempty), ↑t ⊆ s ∧ t.sup' ht f = a := by
  classical
  constructor
  · rintro ⟨T, hT, hTs, rfl⟩
    obtain ⟨t, hts, rfl⟩ := Finset.subset_set_image_iff.1 hTs
    exact ⟨t, Finset.image_nonempty.1 hT, hts, by simp [Finset.sup'_image]⟩
  · rintro ⟨t, ht, hts, rfl⟩
    exact finsetSup'_mem_supClosure ht fun i hi ↦ Set.mem_image_of_mem f (hts hi)

end SemilatticeSup

@[to_dual]
theorem sInf_supClosure [CompleteLattice α] (s : Set α) : sInf (supClosure s) = sInf s :=
  le_antisymm (sInf_le_sInf subset_supClosure) <| le_sInf <| supClosure_min
    (fun _ ↦ sInf_le) fun _ ha _ _ ↦ le_sup_of_le_left ha

/-! ### Greatest elements of lower sets -/

section Greatest

/-- A lower set avoiding every element of `t` lies below `a` when each element not below `a` lies
above some element of `t`. -/
theorem IsLowerSet.isGreatest_of_forall_not_le [Preorder α] {s : Set α} (hs : IsLowerSet s)
    {a : α} (ha : a ∈ s) {t : Finset α} (ht : ∀ b, ¬ b ≤ a → ∃ c ∈ t, c ≤ b)
    (hst : ∀ c ∈ t, c ∉ s) : IsGreatest s a :=
  ⟨ha, fun b hb ↦ by_contra fun hn ↦ let ⟨c, hc, hcb⟩ := ht b hn; hst c hc (hs hcb hb)⟩

variable [SemilatticeSup α] {s : Set α}

/-- A finite nonempty sup-closed set has a greatest element, the sup of its members. -/
theorem SupClosed.exists_isGreatest (hs : SupClosed s) (hfin : s.Finite) (hne : s.Nonempty) :
    ∃ a, IsGreatest s a :=
  ⟨hfin.toFinset.sup' (hfin.toFinset_nonempty.2 hne) id,
    hs.finsetSup'_mem _ fun _ h ↦ hfin.mem_toFinset.1 h,
    fun _ h ↦ Finset.le_sup' id (hfin.mem_toFinset.2 h)⟩

/-- A finite lower set has a greatest element exactly when it is nonempty and sup-closed. -/
theorem IsLowerSet.exists_isGreatest_iff (hs : IsLowerSet s) (hfin : s.Finite) :
    (∃ a, IsGreatest s a) ↔ s.Nonempty ∧ SupClosed s :=
  ⟨fun ⟨a, ha⟩ ↦ ⟨⟨a, ha.1⟩, fun _ hx _ hy ↦ hs (sup_le (ha.2 hx) (ha.2 hy)) ha.1⟩,
    fun ⟨hne, hsc⟩ ↦ hsc.exists_isGreatest hfin hne⟩

variable {β : Type*} [Preorder β] {f : α → β} {U : Set β} {a : α}

/-- The value of an antitone map at the greatest point it sends into `U` is least among its
values in `U`. -/
theorem IsGreatest.isLeast_range_inter (h : IsGreatest (f ⁻¹' U) a) (hf : Antitone f) :
    IsLeast (Set.range f ∩ U) (f a) := by
  simpa only [Set.image_preimage_eq_range_inter] using hf.map_isGreatest h

/-- The value of a monotone map at the least point it sends into `U` is least among its values
in `U`. -/
theorem IsLeast.isLeast_range_inter (h : IsLeast (f ⁻¹' U) a) (hf : Monotone f) :
    IsLeast (Set.range f ∩ U) (f a) := by
  simpa only [Set.image_preimage_eq_range_inter] using hf.map_isLeast h

/-- For an order-reversing embedding `f`, the value at `a` is least among the values of `f` in
`U` exactly when `a` is greatest among the points that `f` sends into `U`. -/
theorem isLeast_range_inter_iff (hf : ∀ a b, f a ≤ f b ↔ b ≤ a) :
    IsLeast (Set.range f ∩ U) (f a) ↔ IsGreatest (f ⁻¹' U) a :=
  ⟨fun h ↦ ⟨h.1.2, fun b hb ↦ (hf a b).1 (h.2 ⟨⟨b, rfl⟩, hb⟩)⟩,
    fun h ↦ h.isLeast_range_inter fun _ _ hba ↦ (hf _ _).2 hba⟩

/-- For an order-reversing embedding `f` of a finite semilattice and an upper set `U`, the values
of `f` in `U` have a least element exactly when the points that `f` sends into `U` are nonempty
and sup-closed. -/
theorem exists_isLeast_range_inter_iff [Finite α] (hf : ∀ a b, f a ≤ f b ↔ b ≤ a)
    (hU : IsUpperSet U) :
    (∃ b, IsLeast (Set.range f ∩ U) b) ↔ (f ⁻¹' U).Nonempty ∧ SupClosed (f ⁻¹' U) := by
  have hl : IsLowerSet (f ⁻¹' U) := fun a b hba ha ↦ hU ((hf a b).2 hba) ha
  rw [← hl.exists_isGreatest_iff (Set.toFinite _)]
  refine ⟨fun ⟨_, h⟩ ↦ ?_, fun ⟨a, ha⟩ ↦ ⟨f a, (isLeast_range_inter_iff hf).2 ha⟩⟩
  obtain ⟨⟨a, rfl⟩, -⟩ := h.1
  exact ⟨a, (isLeast_range_inter_iff hf).1 h⟩

end Greatest

namespace Set

variable {W : Type*} {f : ι → Set W} {s : Set ι} {q : Set W}

theorem mem_supClosure_image :
    q ∈ supClosure (f '' s) ↔ ∃ t : Finset ι, t.Nonempty ∧ ↑t ⊆ s ∧ ⋃ i ∈ t, f i = q := by
  simp only [_root_.mem_supClosure_image, Finset.sup'_eq_sup, Finset.sup_set_eq_biUnion]
  exact ⟨fun ⟨t, ht, h⟩ ↦ ⟨t, ht, h⟩, fun ⟨t, ht, h⟩ ↦ ⟨t, ht, h⟩⟩

theorem mem_infClosure_image :
    q ∈ infClosure (f '' s) ↔ ∃ t : Finset ι, t.Nonempty ∧ ↑t ⊆ s ∧ ⋂ i ∈ t, f i = q := by
  simp only [_root_.mem_infClosure_image, Finset.inf'_eq_inf, Finset.inf_set_eq_iInter]
  exact ⟨fun ⟨t, ht, h⟩ ↦ ⟨t, ht, h⟩, fun ⟨t, ht, h⟩ ↦ ⟨t, ht, h⟩⟩

theorem mem_supClosure_range :
    q ∈ supClosure (Set.range f) ↔ ∃ t : Finset ι, t.Nonempty ∧ ⋃ i ∈ t, f i = q := by
  simp [← Set.image_univ, Set.mem_supClosure_image]

theorem mem_infClosure_range :
    q ∈ infClosure (Set.range f) ↔ ∃ t : Finset ι, t.Nonempty ∧ ⋂ i ∈ t, f i = q := by
  simp [← Set.image_univ, Set.mem_infClosure_image]

theorem supClosure_range_eq_image :
    supClosure (Set.range f) = (fun t : Finset ι ↦ ⋃ i ∈ t, f i) '' {t | t.Nonempty} := by
  ext q
  simp only [Set.mem_supClosure_range, Set.mem_image, Set.mem_ofPred_eq]

theorem infClosure_range_eq_image :
    infClosure (Set.range f) = (fun t : Finset ι ↦ ⋂ i ∈ t, f i) '' {t | t.Nonempty} := by
  ext q
  simp only [Set.mem_infClosure_range, Set.mem_image, Set.mem_ofPred_eq]

theorem sInter_supClosure (S : Set (Set W)) : ⋂₀ supClosure S = ⋂₀ S :=
  _root_.sInf_supClosure S

end Set
