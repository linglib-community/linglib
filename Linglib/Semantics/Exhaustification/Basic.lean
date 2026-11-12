module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Monotone.Basic

/-!
# Exhaustification

This file defines Chierchia's exhaustification operator `O` and its exclusion component.
`excludes C p` holds at the worlds where every true alternative in `C` is entailed by the
prejacent `p`, which is the assertion of the entailment-scale *only*. `exh C p` is the prejacent
together with `excludes C p`: it denies every alternative the prejacent does not entail, so a
member of `C` is exhaustified [where it is the least true
member](##mem_exh_iff_isLeast_of_mem), on a scale where its index is [the greatest true
one](##mem_exh_range_iff_isGreatest). Denying only the strictly stronger alternatives instead
gives [the minimal true members](##mem_exh_inter_Iio_iff_minimal), the same thing [when no
alternative is independent of the prejacent](##exh_inter_Iio_eq_exh). Over finitely many worlds
and an indexed family of alternatives, membership in `exh` is decidable.

## Main statements

* `Exhaustification.exh_eq_sdiff`: `exh` removes from the prejacent the alternatives it does not
  entail.
* `Exhaustification.Irredundant.excludes_injOn`: over an irredundant family, exclusion separates
  the alternative sets that contain the prejacent.
* `Exhaustification.exh_setOf_not_dominated`: among finitely many alternatives, the dominated ones
  change no exhaustification.

## References

* [horn-1969]
* [rooth-1992]
* [von-fintel-1999]
* [chierchia-2006]
* [fox-katzir-2011]
* [enguehard-2025]
-/

@[expose] public section

namespace Exhaustification

variable {W : Type*}

/-! ### Exclusion and exhaustification -/

section Exh

variable {C C' : Set (Set W)} {p q : Set W} {w : W}

/-- `excludes C p` holds at the worlds where every true alternative in `C` is entailed by
`p`. -/
def excludes (C : Set (Set W)) (p : Set W) : Set W := {w | ∀ q ∈ C, w ∈ q → p ⊆ q}

@[simp] theorem mem_excludes : w ∈ excludes C p ↔ ∀ q ∈ C, w ∈ q → p ⊆ q := Iff.rfl

/-- The prejacent `p` with every alternative it does not entail denied
([chierchia-2006]'s `O`). -/
def exh (C : Set (Set W)) (p : Set W) : Set W := p ∩ excludes C p

@[simp] theorem mem_exh : w ∈ exh C p ↔ w ∈ p ∧ ∀ q ∈ C, w ∈ q → p ⊆ q := Iff.rfl

theorem exh_subset (C : Set (Set W)) (p : Set W) : exh C p ⊆ p := fun _ h ↦ h.1

theorem exh_subset_excludes (C : Set (Set W)) (p : Set W) : exh C p ⊆ excludes C p :=
  fun _ h ↦ h.2

theorem notMem_excludes (hq : q ∈ C) (hw : w ∈ q) (h : ¬ p ⊆ q) : w ∉ excludes C p :=
  fun he ↦ h (he q hq hw)

theorem notMem_exh (hq : q ∈ C) (hw : w ∈ q) (h : ¬ p ⊆ q) : w ∉ exh C p :=
  fun he ↦ notMem_excludes hq hw h he.2

theorem exh_subset_compl (hq : q ∈ C) (h : ¬ p ⊆ q) : exh C p ⊆ qᶜ :=
  fun _ hw hwq ↦ notMem_exh hq hwq h hw

/-- A member of `C` is exhaustified where it is the least true member under entailment, the
strongest alternative true there. -/
theorem mem_exh_iff_isLeast_of_mem (hp : p ∈ C) : w ∈ exh C p ↔ IsLeast {q ∈ C | w ∈ q} p :=
  ⟨fun ⟨hw, h⟩ ↦ ⟨⟨hp, hw⟩, fun q ⟨hq, hwq⟩ ↦ h q hq hwq⟩,
    fun ⟨⟨_, hw⟩, h⟩ ↦ ⟨hw, fun _ hq hwq ↦ h ⟨hq, hwq⟩⟩⟩

theorem mem_exh_image_iff {ι : Type*} {f : ι → Set W} {A : Set ι} :
    w ∈ exh (f '' A) p ↔ w ∈ p ∧ ∀ i ∈ A, w ∈ f i → p ⊆ f i := by
  simp only [mem_exh, Set.forall_mem_image]

theorem mem_exh_range_iff {ι : Type*} {f : ι → Set W} :
    w ∈ exh (Set.range f) p ↔ w ∈ p ∧ ∀ i, w ∈ f i → p ⊆ f i := by
  simp only [mem_exh, Set.forall_mem_range]

/-- Over finite worlds and indices, exhaustifying against an indexed family is decidable. -/
instance [Fintype W] {ι : Type*} [Fintype ι] {f : ι → Set W} [∀ i, DecidablePred (· ∈ f i)]
    {A : Set ι} [DecidablePred (· ∈ A)] {p : Set W} [DecidablePred (· ∈ p)] :
    DecidablePred (· ∈ exh (f '' A) p) := fun w ↦
  decidable_of_iff (w ∈ p ∧ ∀ i, i ∈ A → w ∈ f i → ∀ x, x ∈ p → x ∈ f i) mem_exh_image_iff.symm

instance [Fintype W] {ι : Type*} [Fintype ι] {f : ι → Set W} [∀ i, DecidablePred (· ∈ f i)]
    {p : Set W} [DecidablePred (· ∈ p)] : DecidablePred (· ∈ exh (Set.range f) p) := fun w ↦
  decidable_of_iff (w ∈ p ∧ ∀ i, w ∈ f i → ∀ x, x ∈ p → x ∈ f i) mem_exh_range_iff.symm

theorem mem_excludes_of_forall_notMem (h : ∀ q ∈ C, ¬ p ⊆ q → w ∉ q) : w ∈ excludes C p :=
  fun q hq hwq ↦ not_not.mp fun hne ↦ h q hq hne hwq

theorem excludes_eq_compl_sUnion (C : Set (Set W)) (p : Set W) :
    excludes C p = (⋃₀ {q ∈ C | ¬ p ⊆ q})ᶜ := by
  ext w
  simp only [mem_excludes, Set.mem_compl_iff, Set.mem_sUnion, Set.mem_ofPred_eq, not_exists,
    not_and, and_imp]
  exact ⟨fun h q hq hpq hw ↦ hpq (h q hq hw), fun h q hq hw ↦ not_not.mp fun hpq ↦ h q hq hpq hw⟩

theorem exh_eq_sdiff (C : Set (Set W)) (p : Set W) : exh C p = p \ ⋃₀ {q ∈ C | ¬ p ⊆ q} := by
  rw [exh, excludes_eq_compl_sUnion, Set.sdiff_eq]

theorem exh_eq_self_iff : exh C p = p ↔ ∀ q ∈ C, (p ∩ q).Nonempty → p ⊆ q :=
  ⟨fun h q hq ⟨w, hw, hwq⟩ ↦ by rw [← h] at hw; exact hw.2 q hq hwq,
    fun h ↦ (exh_subset C p).antisymm fun w hw ↦ ⟨hw, fun q hq hwq ↦ h q hq ⟨w, hw, hwq⟩⟩⟩

theorem exh_eq_self (h : ∀ q ∈ C, p ⊆ q) : exh C p = p :=
  exh_eq_self_iff.2 fun q hq _ ↦ h q hq

@[simp] theorem exh_empty (p : Set W) : exh ∅ p = p := exh_eq_self fun _ h ↦ h.elim

/-- An alternative the prejacent entails is inert. -/
theorem exh_insert_of_subset (h : p ⊆ q) : exh (insert q C) p = exh C p :=
  Set.ext fun _ ↦ and_congr_right fun _ ↦ ⟨fun hw r hr ↦ hw r (.inr hr),
    fun hw r hr hwr ↦ hr.elim (fun e ↦ e ▸ h) (hw r · hwr)⟩

/-- An alternative the prejacent does not entail is denied. -/
theorem exh_insert_of_not_subset (h : ¬ p ⊆ q) : exh (insert q C) p = exh C p \ q :=
  Set.ext fun _ ↦ ⟨fun ⟨hp, hw⟩ ↦
      ⟨⟨hp, fun r hr ↦ hw r (.inr hr)⟩, fun hq ↦ h (hw q (.inl rfl) hq)⟩,
    fun ⟨⟨hp, hw⟩, hq⟩ ↦ ⟨hp, fun r hr hwr ↦
      hr.elim (fun e ↦ absurd (e ▸ hwr) hq) (hw r · hwr)⟩⟩

theorem exh_singleton_of_not_subset (h : ¬ p ⊆ q) : exh {q} p = p \ q := by
  rw [← insert_empty_eq, exh_insert_of_not_subset h, exh_empty]

theorem excludes_antitone (h : C ⊆ C') (p : Set W) : excludes C' p ⊆ excludes C p :=
  fun _ hw q hq ↦ hw q (h hq)

theorem exh_antitone (h : C ⊆ C') (p : Set W) : exh C' p ⊆ exh C p :=
  Set.inter_subset_inter_right _ (excludes_antitone h p)

theorem antitone_excludes (C : Set (Set W)) : Antitone (excludes C) :=
  fun _ _ hpq _ hw r hr hwr ↦ hpq.trans (hw r hr hwr)

theorem excludes_union (C : Set (Set W)) (p q : Set W) :
    excludes C (p ∪ q) = excludes C p ∩ excludes C q := by
  ext w
  simp only [mem_excludes, Set.union_subset_iff, Set.mem_inter_iff, imp_and, forall_and]

theorem mem_excludes_iff_forall_eq (h : ∀ q ∈ C, p ⊆ q → q = p) :
    w ∈ excludes C p ↔ ∀ q ∈ C, w ∈ q → q = p :=
  forall₂_congr fun q hq ↦ imp_congr_right fun _ ↦ ⟨h q hq, fun hqp ↦ hqp ▸ subset_rfl⟩

end Exh

/-! ### Irredundant alternatives -/

section Irredundant

variable {ι : Type*} {f : ι → Set W}

/-- A family of alternatives is **irredundant** when each member can hold while every other
member fails, so that no member is covered by the union of the rest. Strictly weaker than the mutual
exclusivity of partition semantics (`irredundant_of_pairwise_disjoint`). -/
def Irredundant (f : ι → Set W) : Prop :=
  ∀ i, ∃ w ∈ f i, ∀ j, j ≠ i → w ∉ f j

theorem irredundant_of_pairwise_disjoint (hd : Pairwise fun i j ↦ Disjoint (f i) (f j))
    (hne : ∀ i, (f i).Nonempty) : Irredundant f := fun i ↦
  let ⟨w, hw⟩ := hne i
  ⟨w, hw, fun _ hj hwj ↦ Set.disjoint_left.mp (hd hj) hwj hw⟩

theorem Irredundant.not_subset (hf : Irredundant f) {i j : ι} (hij : i ≠ j) : ¬ f i ⊆ f j :=
  let ⟨_, hw, hother⟩ := hf i
  fun h ↦ hother j hij.symm (h hw)

theorem Irredundant.excludes_ne (hf : Irredundant f) {i₀ j : ι} {s₁ s₂ : Finset ι}
    (hj₂ : j ∈ s₂) (hj₁ : j ∉ s₁) (hji : j ≠ i₀) :
    excludes (f '' ↑s₁) (f i₀) ≠ excludes (f '' ↑s₂) (f i₀) := by
  obtain ⟨w, hwj, hother⟩ := hf j
  refine ne_of_mem_of_not_mem' (mem_excludes_of_forall_notMem ?_)
    (notMem_excludes ⟨j, hj₂, rfl⟩ hwj (hf.not_subset hji.symm))
  rintro q ⟨k, hk, rfl⟩ _
  exact hother k fun h ↦ hj₁ (h ▸ hk)

theorem Irredundant.excludes_injOn (hf : Irredundant f) (i₀ : ι) :
    Set.InjOn (fun s : Finset ι ↦ excludes (f '' ↑s) (f i₀)) {s | i₀ ∈ s} := by
  intro s₁ h₁ s₂ h₂ heq
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, ¬ (j ∈ s₁ ↔ j ∈ s₂) := by simpa [Finset.ext_iff] using hne
  by_cases hmem : j ∈ s₁
  · have h₂j : j ∉ s₂ := fun h ↦ hj ⟨fun _ ↦ h, fun _ ↦ hmem⟩
    exact hf.excludes_ne hmem h₂j (fun h ↦ h₂j (h ▸ h₂)) heq.symm
  · have h₂j : j ∈ s₂ := by
      by_contra h2
      exact hj ⟨fun h ↦ absurd h hmem, fun h ↦ absurd h h2⟩
    exact hf.excludes_ne h₂j hmem (fun h ↦ hmem (h ▸ h₁)) heq

/-- Over an irredundant family, a member is exhaustified where it is the only true member. -/
theorem Irredundant.mem_exh_range_iff (hf : Irredundant f) {i : ι} {w : W} :
    w ∈ exh (Set.range f) (f i) ↔ w ∈ f i ∧ ∀ j, w ∈ f j → j = i :=
  Exhaustification.mem_exh_range_iff.trans <| and_congr_right fun _ ↦ forall_congr' fun _ ↦
    imp_congr_right fun _ ↦
    ⟨fun h ↦ by_contra fun hne ↦ hf.not_subset (Ne.symm hne) h, fun h ↦ h ▸ subset_rfl⟩

/-- When the members a member entails are those at the indices below its own, it is exhaustified
where its index is the greatest true one. -/
theorem mem_exh_range_iff_isGreatest_of_forall [Preorder ι] {i : ι} {w : W}
    (hf : ∀ j, f i ⊆ f j ↔ j ≤ i) : w ∈ exh (Set.range f) (f i) ↔ IsGreatest {j | w ∈ f j} i :=
  mem_exh_range_iff.trans <| and_congr_right fun _ ↦ forall_congr' fun j ↦ imp_congr_right fun _ ↦
    hf j

section LinearOrder

variable [LinearOrder ι] {i : ι} {w : W}

/-- On a strictly decreasing family, where larger indices are stronger, a member is exhaustified
where its index is the greatest true one. -/
theorem mem_exh_range_iff_isGreatest (hf : StrictAnti f) :
    w ∈ exh (Set.range f) (f i) ↔ IsGreatest {j | w ∈ f j} i :=
  mem_exh_range_iff_isGreatest_of_forall fun _ ↦ hf.le_iff_ge

/-- On a strictly increasing family, where smaller indices are stronger, a member is exhaustified
where its index is the least true one. -/
theorem mem_exh_range_iff_isLeast (hf : StrictMono f) :
    w ∈ exh (Set.range f) (f i) ↔ IsLeast {j | w ∈ f j} i :=
  mem_exh_range_iff.trans <| and_congr_right fun _ ↦ forall_congr' fun _ ↦ imp_congr_right fun _ ↦
    hf.le_iff_le

end LinearOrder

end Irredundant

/-! ### Domination -/

section Dominated

variable {C : Set (Set W)} {p q q₁ q₂ : Set W} {w : W}

/-- A member is dominated when the members strictly stronger than it cover it, the condition
[enguehard-2025] gives (25). A dominated member is never the strongest true one. -/
def Dominated (C : Set (Set W)) (p : Set W) : Prop := p ⊆ ⋃₀ (C ∩ Set.Iio p)

theorem mem_excludes_inter_Iio : w ∈ excludes (C ∩ Set.Iio p) p ↔ ∀ q ∈ C, q ⊂ p → w ∉ q :=
  ⟨fun h q hq hqp hw ↦ hqp.2 (h q ⟨hq, hqp⟩ hw), fun h q hq hw ↦ (h q hq.1 hq.2 hw).elim⟩

/-- Exhaustifying against the strictly stronger alternatives negates all of them. -/
theorem mem_exh_inter_Iio : w ∈ exh (C ∩ Set.Iio p) p ↔ w ∈ p ∧ ∀ q ∈ C, q ⊂ p → w ∉ q :=
  and_congr_right fun _ ↦ mem_excludes_inter_Iio

/-- Exhaustified against the strictly stronger alternatives only, a member of `C` holds where it
is a minimal true member: true, with no true member strictly below it. -/
theorem mem_exh_inter_Iio_iff_minimal (hp : p ∈ C) :
    w ∈ exh (C ∩ Set.Iio p) p ↔ Minimal (· ∈ {q ∈ C | w ∈ q}) p :=
  mem_exh_inter_Iio.trans <| Iff.trans
    ⟨fun ⟨hw, h⟩ ↦ ⟨⟨hp, hw⟩, fun _ hlt hy ↦ h _ hy.1 hlt hy.2⟩,
      fun ⟨hw, h⟩ ↦ ⟨hw.2, fun _ hq hlt hwq ↦ h hlt ⟨hq, hwq⟩⟩⟩
    minimal_iff_forall_lt.symm

/-- Denying the alternatives the prejacent does not entail denies the strictly stronger ones. -/
theorem exh_subset_exh_inter_Iio (C : Set (Set W)) (p : Set W) :
    exh C p ⊆ exh (C ∩ Set.Iio p) p :=
  exh_antitone Set.inter_subset_left p

/-- When every alternative is comparable with the prejacent, the alternatives it does not entail
are the strictly stronger ones, and the two exhaustifications agree. They come apart on an
alternative that is independent of the prejacent, which only `exh C p` denies. -/
theorem exh_inter_Iio_eq_exh (h : ∀ q ∈ C, q ⊆ p ∨ p ⊆ q) : exh (C ∩ Set.Iio p) p = exh C p :=
  (exh_subset_exh_inter_Iio C p).antisymm' fun _ hw ↦ ⟨hw.1, fun q hq hwq ↦
    (h q hq).elim (fun hqp ↦ not_not.1 fun hpq ↦ (mem_exh_inter_Iio.1 hw).2 q hq ⟨hqp, hpq⟩ hwq) id⟩

/-- A member is dominated exactly when negating what is strictly stronger leaves nothing. -/
theorem exh_inter_Iio_eq_empty_iff : exh (C ∩ Set.Iio p) p = ∅ ↔ Dominated C p := by
  simp only [Set.eq_empty_iff_forall_notMem, mem_exh_inter_Iio, Dominated, Set.subset_def,
    Set.mem_sUnion, Set.mem_inter_iff, Set.mem_Iio, not_and, not_forall, not_not]
  exact forall_congr' fun w ↦ forall_congr' fun _ ↦
    ⟨fun ⟨q, hq, hqp, hw⟩ ↦ ⟨q, ⟨hq, hqp⟩, hw⟩, fun ⟨q, ⟨hq, hqp⟩, hw⟩ ↦ ⟨q, hq, hqp, hw⟩⟩

theorem exh_eq_empty_of_dominated (h : Dominated C p) : exh C p = ∅ :=
  Set.subset_empty_iff.1 <|
    exh_inter_Iio_eq_empty_iff.2 h ▸ exh_antitone Set.inter_subset_left p

/-- The union of two members neither of which entails the other is dominated by them. -/
theorem dominated_union (h₁ : q₁ ∈ C) (h₂ : q₂ ∈ C) (h₁₂ : ¬ q₁ ⊆ q₂) (h₂₁ : ¬ q₂ ⊆ q₁) :
    Dominated C (q₁ ∪ q₂) := by
  rintro w (hw | hw)
  · exact ⟨q₁, ⟨h₁, Set.subset_union_left.ssubset_of_not_subset fun h ↦
      h₂₁ (Set.subset_union_right.trans h)⟩, hw⟩
  · exact ⟨q₂, ⟨h₂, Set.subset_union_right.ssubset_of_not_subset fun h ↦
      h₁₂ (Set.subset_union_left.trans h)⟩, hw⟩

/-- Among finitely many alternatives, a true one lies above a true one that is not dominated. -/
theorem exists_mem_subset_not_dominated (hC : C.Finite) (hq : q ∈ C) (hw : w ∈ q) :
    ∃ m ∈ C, ¬ Dominated C m ∧ w ∈ m ∧ m ⊆ q := by
  obtain ⟨m, hmq, hm⟩ := (hC.subset (Set.sep_subset C (w ∈ ·))).exists_le_minimal
    (show q ∈ {m ∈ C | w ∈ m} from ⟨hq, hw⟩)
  refine ⟨m, hm.1.1, fun hd ↦ ?_, hm.1.2, hmq⟩
  obtain ⟨s, ⟨hs, hsm⟩, hws⟩ := hd hm.1.2
  exact hsm.2 (hm.2 ⟨hs, hws⟩ hsm.1)

/-- Among finitely many alternatives, exhaustifying against the members that are not dominated is
exhaustifying against all of them. -/
theorem exh_setOf_not_dominated (hC : C.Finite) (p : Set W) :
    exh {q ∈ C | ¬ Dominated C q} p = exh C p := by
  refine Set.Subset.antisymm (fun w hw ↦ ⟨hw.1, fun q hq hwq ↦ ?_⟩)
    (exh_antitone (fun _ h ↦ h.1) p)
  obtain ⟨m, hm, hmd, hwm, hmq⟩ := exists_mem_subset_not_dominated hC hq hwq
  exact (hw.2 m ⟨hm, hmd⟩ hwm).trans hmq

end Dominated

end Exhaustification
