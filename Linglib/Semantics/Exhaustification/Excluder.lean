module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Basic
public import Linglib.Semantics.Exhaustification.Pointwise

/-!
# Exhaustification

An exhaustification operator asserts a prejacent and denies a selection of its alternatives.
This file defines the selection every theory of *only* and of exhaustification shares, the
alternatives the prejacent does not entail, and the finite excluders that vary it.

`excludes C p` is the exclusion component, holding where every true alternative in `C` is entailed
by `p`. It is the assertion of the entailment-scale *only* (`Focus.Particles.only`), as in Horn,
Rooth and von Fintel, and `exh C p`, the prejacent together with the exclusion, is Chierchia's
operator `O`. Exclusion is anti-additive in the prejacent (`excludes_union`). Over an `Irredundant`
family, where each alternative has a world of its own, exclusion separates resolutions of the
alternative set (`Irredundant.excludes_injOn`), and narrowing the alternatives weakens it
(`excludes_antitone`). Read at a world, `exh` against a family of alternatives is `exhAgainst` the
members the prejacent does not entail (`mem_exh_range_iff_exhAgainst`), over an irredundant family
every other member (`Irredundant.mem_exh_range_iff`). Against the image or range of an indexed
family, `exh` denies the members the prejacent does not entail (`mem_exh_image_iff`), decidably over
finite worlds. When the prejacent is maximal among the alternatives, exclusion is Rooth's condition
that every true alternative *equals* the prejacent (`mem_excludes_iff_forall_eq`).

An `Excluder` is a selection over finite world types, `Excluder.exh` the resulting operator, and
`tolerant` is `exh` there, contradiction or not, after Chierchia. `Excluder.preFilter` offers an
excluder only some of the alternatives, which can strengthen the result, the asymmetry Fox and
Katzir state between the formal alternative source and contextual restriction; restricting the
denied alternatives to the relevant ones, after Magri, is the relevance set of
`Exhaustification.excludesIE`. The innocent excluder is `innocent` in `Finite`.

## References

* [horn-1969]
* [rooth-1992]
* [von-fintel-1999]
* [chierchia-2006]
* [chierchia-2013]
* [fox-2007]
* [fox-katzir-2011]
* [magri-2009]
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

theorem mem_exh_range_iff_exhAgainst (f : ι → Set W) (i : ι) (w : W) :
    w ∈ exh (Set.range f) (f i) ↔ exhAgainst (fun i j ↦ ¬ f i ⊆ f j) (w ∈ f ·) i := by
  simp only [mem_exh, Set.forall_mem_range, exhAgainst]
  exact and_congr_right fun _ ↦ forall_congr' fun j ↦
    ⟨fun h hn hw ↦ hn (h hw), fun h hw ↦ not_not.1 fun hn ↦ h hn hw⟩

theorem Irredundant.mem_exh_range_iff {f : ι → Set W} (hf : Irredundant f) (i : ι) (w : W) :
    w ∈ exh (Set.range f) (f i) ↔ exhAgainst (· ≠ ·) (w ∈ f ·) i := by
  rw [mem_exh_range_iff_exhAgainst]
  refine and_congr_right fun _ ↦ forall_congr' fun j ↦ ⟨fun h hij ↦ h (hf.not_subset hij),
    fun h hn ↦ h fun hij ↦ hn (hij ▸ subset_rfl)⟩

end Irredundant

variable [Fintype W] [DecidableEq W]

/-- The worlds satisfying a `Bool` predicate. -/
def predToFinset (p : W → Bool) : Finset W :=
  Finset.univ.filter (fun w => p w)

/-- The alternative set of a list of `Bool` predicates. -/
def altsFromPreds (alts : List (W → Bool)) : Finset (Finset W) :=
  (alts.map predToFinset).toFinset

@[simp] theorem altsFromPreds_singleton (p : W → Bool) :
    altsFromPreds [p] = ({predToFinset p} : Finset (Finset W)) := by
  simp [altsFromPreds]

/-- A choice, for each alternative set and prejacent, of the alternatives to deny. -/
structure Excluder (W : Type*) [Fintype W] [DecidableEq W] where
  /-- Given a prejacent `φ` and an alternative set `ALT`, return the
      alternatives whose negation should be conjoined with `φ`. -/
  excluded : Finset (Finset W) → Finset W → Finset (Finset W)
  /-- The strategy returns a sub-collection of the offered alternatives. -/
  excluded_subset : ∀ ALT φ, excluded ALT φ ⊆ ALT

namespace Excluder

variable (E : Excluder W) (ALT : Finset (Finset W)) (φ : Finset W)

/-- The prejacent with every excluded alternative denied. -/
def exh : Finset W :=
  φ \ (E.excluded ALT φ).biUnion id

theorem exh_subset_phi : E.exh ALT φ ⊆ φ := Finset.sdiff_subset

theorem mem_exh_iff {w : W} :
    w ∈ E.exh ALT φ ↔ w ∈ φ ∧ ∀ a ∈ E.excluded ALT φ, w ∉ a := by
  simp only [exh, Finset.mem_sdiff, Finset.mem_biUnion, id_eq, not_exists, not_and]

/-! ### Filtering the offered alternatives -/

/-- Offer the excluder only the alternatives in `K`. -/
def preFilter (K : Finset (Finset W)) : Excluder W where
  excluded A ψ := E.excluded (A ∩ K) ψ
  excluded_subset _ _ := (E.excluded_subset _ _).trans Finset.inter_subset_left

@[simp] theorem preFilter_excluded (K : Finset (Finset W)) :
    (E.preFilter K).excluded ALT φ = E.excluded (ALT ∩ K) φ := rfl

end Excluder

/-! ### The tolerant excluder -/

/-- The tolerant excluder denies every alternative not entailed by the prejacent. -/
def tolerant : Excluder W where
  excluded ALT φ := ALT.filter (fun a => ¬ φ ⊆ a)
  excluded_subset _ _ := Finset.filter_subset _ _

@[simp] theorem tolerant_excluded (ALT : Finset (Finset W)) (φ : Finset W) :
    tolerant.excluded ALT φ = ALT.filter (fun a => ¬ φ ⊆ a) := rfl

theorem mem_tolerant_excluded {ALT : Finset (Finset W)} {φ a : Finset W} :
    a ∈ tolerant.excluded ALT φ ↔ a ∈ ALT ∧ ¬ φ ⊆ a := by
  simp [tolerant_excluded, Finset.mem_filter]

theorem mem_tolerant_exh_iff (ALT : Finset (Finset W)) (φ : Finset W) {w : W} :
    w ∈ tolerant.exh ALT φ ↔ w ∈ φ ∧ ∀ a ∈ ALT, ¬ φ ⊆ a → w ∉ a := by
  rw [Excluder.mem_exh_iff]
  refine and_congr_right (fun _ => ?_)
  simp [tolerant_excluded, Finset.mem_filter, and_imp]

theorem entailed_not_excluded {ALT : Finset (Finset W)} {φ a : Finset W}
    (h : φ ⊆ a) : a ∉ tolerant.excluded ALT φ := by
  simp [h]

end Exhaustification
