module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Closure
public import Linglib.Core.Order.Concept

/-!
# Compatibility frames

This file defines compatibility frames, the possibility semantics for orthologic on which
Holliday and Mandelkern build their account of epistemic modals, and the ortholattice of regular
propositions of a frame. A compatibility frame is a set of partial *possibilities* with a
reflexive, symmetric compatibility relation, and
[a possibility can settle a disjunction without settling either disjunct](##mem_disj). The
propositions are the *regular* sets, negation is the orthocomplement, and
[the regular sets are the concept extents of orthogonality](##isRegular_iff_isExtent), so they
form an ortholattice that need not be Boolean. A possibility
[refines `x` when it makes true every proposition true at `x`](##refines_iff_forall_isRegular),
and [the refinements of `x` form a proposition](##refines_iff_mem_orthoNeg_orthoNeg), that `x`
obtains.

## Main definitions

* `CompatFrame`: a set of possibilities with a reflexive, symmetric compatibility relation.
* `orthoNeg`, `disj`: orthocomplement negation and De Morgan disjunction.
* `IsRegular`, `refines`, `IsWorld`: regularity, refinement, and worlds.
* `CompatFrame.Regular`: the ortholattice of regular propositions.

## Implementation notes

A frame also carries its orthogonality relation `ortho`, the complement of compatibility, which
defaults to `¬ compat` and is stored as data in the way `Preorder` stores `<`. The regular
propositions are the concepts of `ortho` (`Core/Order/Concept.lean`), so closure properties of
regular sets are those of mathlib's `Order.IsExtent`, and the paper's closure operator $c_◇$ is
mathlib's `extentClosure`. A frame built from an orthogonality relation, such as the canonical
frame of an ortholattice, keeps that relation definitionally. Decidability of `compat` is not
bundled: use sites take `[DecidableRel F.compat]`, as for `SimpleGraph.Adj`. The paper's frames
are nonempty; no result here needs it, so the structure does not require it.

## References

* [holliday-mandelkern-2024]
-/

@[expose] public section

namespace Orthologic

open Order

variable {S : Type*}

/-! ### Compatibility frames -/

/-- A compatibility frame is a set of possibilities with a reflexive, symmetric compatibility
    relation; two possibilities are compatible when neither settles as true anything the other
    settles as false ([holliday-mandelkern-2024] Definition 4.1). -/
structure CompatFrame (S : Type*) where
  /-- Compatibility of possibilities. -/
  compat : S → S → Prop
  compat_refl : Std.Refl compat
  compat_symm : Std.Symm compat
  /-- Orthogonality, the complement of compatibility. -/
  ortho : S → S → Prop := fun x y ↦ ¬ compat x y
  ortho_iff : ∀ x y, ortho x y ↔ ¬ compat x y := by intros; exact Iff.rfl

namespace CompatFrame

/-- Compatibility is reflexive. -/
theorem refl (F : CompatFrame S) (x : S) : F.compat x x := F.compat_refl.refl x

/-- Compatibility is symmetric, as `SimpleGraph.Adj.symm` is for adjacency. -/
theorem compat.symm {F : CompatFrame S} {x y : S} (h : F.compat x y) : F.compat y x :=
  F.compat_symm.symm x y h

instance (F : CompatFrame S) : Std.Symm F.ortho :=
  ⟨fun x y h ↦ (F.ortho_iff y x).mpr fun hc ↦ (F.ortho_iff x y).mp h hc.symm⟩

instance (F : CompatFrame S) : Std.Irrefl F.ortho :=
  ⟨fun x h ↦ (F.ortho_iff x x).mp h (F.refl x)⟩

instance (F : CompatFrame S) [DecidableRel F.compat] : DecidableRel F.ortho :=
  fun x y ↦ decidable_of_iff _ (F.ortho_iff x y).symm

end CompatFrame

variable (F : CompatFrame S)

/-! ### Orthocomplement negation and disjunction -/

/-- The orthocomplement `¬A` holds at the possibilities compatible with no `A`-possibility,
    those whose information settles `¬A` ([holliday-mandelkern-2024] Proposition 4.8,
    eq. (1)). -/
def orthoNeg (A : Set S) : Set S :=
  { x | ∀ y : S, F.compat x y → y ∉ A }

@[simp] theorem mem_orthoNeg (A : Set S) (x : S) :
    x ∈ orthoNeg F A ↔ ∀ y : S, F.compat x y → y ∉ A := Iff.rfl

instance [Fintype S] [DecidableRel F.compat] (A : Set S) [DecidablePred (· ∈ A)] (x : S) :
    Decidable (x ∈ orthoNeg F A) :=
  inferInstanceAs (Decidable (∀ y : S, F.compat x y → y ∉ A))

/-- The De Morgan disjunction `A ∨ B = ¬(¬A ∩ ¬B)` ([holliday-mandelkern-2024] Proposition 4.8). -/
def disj (A B : Set S) : Set S :=
  orthoNeg F (orthoNeg F A ∩ orthoNeg F B)

instance [Fintype S] [DecidableRel F.compat] (A B : Set S) [DecidablePred (· ∈ A)]
    [DecidablePred (· ∈ B)] (x : S) : Decidable (x ∈ disj F A B) :=
  inferInstanceAs (Decidable (x ∈ orthoNeg F (orthoNeg F A ∩ orthoNeg F B)))

/-- `x` makes `A ∨ B` true iff every possibility compatible with `x` is compatible with one making
`A` or `B` true, so a possibility can settle a disjunction without settling either disjunct
([holliday-mandelkern-2024] eq. (2)). -/
theorem mem_disj {A B : Set S} {x : S} :
    x ∈ disj F A B ↔ ∀ y, F.compat x y → ∃ z, F.compat y z ∧ (z ∈ A ∨ z ∈ B) := by
  simp only [disj, mem_orthoNeg, Set.mem_inter_iff, not_and_or, not_forall, not_not,
    exists_prop, and_or_left, exists_or]

/-- When compatibility is identity, as between the possible worlds of classical semantics,
orthocomplement is Boolean complement ([holliday-mandelkern-2024] pp. 858 and 861). -/
theorem orthoNeg_eq_compl (h : ∀ x y, F.compat x y → x = y) (A : Set S) :
    orthoNeg F A = Aᶜ :=
  Set.ext fun x ↦ ⟨fun hx hA ↦ hx x (F.refl x) hA, fun hx y hxy ↦ h x y hxy ▸ hx⟩

/-! ### Regularity -/

/-- A set `A` is regular when every possibility outside `A` is compatible with one all of whose
    compatible possibilities lie outside `A`; only regular sets count as propositions
    ([holliday-mandelkern-2024] Definition 4.3). -/
def IsRegular (A : Set S) : Prop :=
  ∀ x : S, x ∈ A ∨ ∃ y : S, F.compat x y ∧ ∀ z : S, F.compat y z → z ∉ A

instance [Fintype S] [DecidableRel F.compat] (A : Set S) [DecidablePred (· ∈ A)] :
    Decidable (IsRegular F A) :=
  inferInstanceAs (Decidable (∀ x : S, x ∈ A ∨ ∃ y : S, F.compat x y ∧ ∀ z, F.compat y z → z ∉ A))

theorem orthoNeg_eq_upperPolar (A : Set S) : orthoNeg F A = upperPolar F.ortho A := by
  ext x
  exact ⟨fun hx a ha ↦ (F.ortho_iff a x).mpr fun hc ↦ hx a hc.symm ha,
    fun hx y hxy hyA ↦ (F.ortho_iff y x).mp (hx hyA) hxy.symm⟩

theorem orthoNeg_eq_lowerPolar (A : Set S) : orthoNeg F A = lowerPolar F.ortho A := by
  rw [orthoNeg_eq_upperPolar, upperPolar_eq_lowerPolar]

/-- Regularity says that `¬¬A ⊆ A`, read contrapositively. -/
theorem isRegular_iff_orthoNeg_orthoNeg_subset (A : Set S) :
    IsRegular F A ↔ orthoNeg F (orthoNeg F A) ⊆ A := by
  simp only [IsRegular, Set.subset_def, or_iff_not_imp_right, mem_orthoNeg, not_exists, not_and,
    not_forall, not_not, exists_prop]

/-- The regular sets of `F` are exactly the concept extents of its orthogonality relation. -/
theorem isRegular_iff_isExtent (A : Set S) : IsRegular F A ↔ IsExtent F.ortho A := by
  rw [isRegular_iff_orthoNeg_orthoNeg_subset, isExtent_iff, orthoNeg_eq_lowerPolar F (orthoNeg F A),
    orthoNeg_eq_upperPolar F A]
  exact ⟨fun h ↦ h.antisymm (subset_lowerPolar_upperPolar ..), Eq.subset⟩

theorem isRegular_orthoNeg (A : Set S) : IsRegular F (orthoNeg F A) := by
  rw [isRegular_iff_isExtent, orthoNeg_eq_lowerPolar]
  exact isExtent_lowerPolar

variable {F} in
/-- Orthocomplementation is involutive on regular sets, `¬¬A = A`
    ([holliday-mandelkern-2024] Proposition 4.8). -/
theorem IsRegular.orthoNeg_orthoNeg {A : Set S} (hA : IsRegular F A) :
    orthoNeg F (orthoNeg F A) = A := by
  rw [orthoNeg_eq_lowerPolar F (orthoNeg F A), orthoNeg_eq_upperPolar F A]
  exact ((isRegular_iff_isExtent F A).1 hA).eq

/-- The closure operator `c_◇` sends `A` to the possibilities all of whose compatible
    possibilities are compatible with an `A`-possibility; it is the extent closure of
    orthogonality, so its fixed points are the regular sets ([holliday-mandelkern-2024]
    footnote 19). -/
theorem mem_extentClosure_ortho {A : Set S} {x : S} :
    x ∈ extentClosure F.ortho A ↔ ∀ y, F.compat x y → ∃ z, F.compat y z ∧ z ∈ A := by
  rw [extentClosure_apply, ← orthoNeg_eq_upperPolar, ← orthoNeg_eq_lowerPolar]
  simp only [mem_orthoNeg, not_forall, not_not, exists_prop]

/-! ### Refinement and worlds -/

/-- A possibility `y` refines `x`, written `y ⊑ x`, when every possibility compatible with `y`
    is compatible with `x`, so that `y` carries at least as much information
    ([holliday-mandelkern-2024] Lemma 4.4, condition 2). -/
def refines (y x : S) : Prop :=
  ∀ z : S, F.compat y z → F.compat x z

instance [Fintype S] [DecidableRel F.compat] (y x : S) : Decidable (refines F y x) :=
  inferInstanceAs (Decidable (∀ z : S, F.compat y z → F.compat x z))

variable {F} in
theorem IsRegular.mem_of_refines {A : Set S} (hA : IsRegular F A) {z x : S} (h : refines F z x)
    (hx : x ∈ A) : z ∈ A :=
  (hA z).resolve_right fun ⟨_, hzw, hw⟩ ↦ hw x (h _ hzw).symm hx

/-- The refinements of `x` are the possibilities settling `¬¬{x}`, so they form a regular set
    ([holliday-mandelkern-2024] Lemma 4.5). -/
theorem refines_iff_mem_orthoNeg_orthoNeg {z x : S} :
    refines F z x ↔ z ∈ orthoNeg F (orthoNeg F {x}) := by
  simp only [refines, mem_orthoNeg, Set.mem_singleton_iff, not_forall, not_not, exists_prop,
    exists_eq_right]
  exact forall₂_congr fun _ _ ↦ ⟨CompatFrame.compat.symm, CompatFrame.compat.symm⟩

/-- A possibility refines `x` iff it makes true every proposition true at `x`
    ([holliday-mandelkern-2024] Lemma 4.4). -/
theorem refines_iff_forall_isRegular {y x : S} :
    refines F y x ↔ ∀ A, IsRegular F A → x ∈ A → y ∈ A :=
  ⟨fun h _ hA ↦ hA.mem_of_refines h, fun h ↦ (refines_iff_mem_orthoNeg_orthoNeg F).2 <|
    h _ (isRegular_orthoNeg F _) ((refines_iff_mem_orthoNeg_orthoNeg F).1 fun _ ↦ id)⟩

/-- A world is a possibility that refines everything it is compatible with, the most
    informative kind of possibility ([holliday-mandelkern-2024] Definition 4.6). -/
def IsWorld (w : S) : Prop :=
  ∀ x : S, F.compat w x → refines F w x

instance [Fintype S] [DecidableRel F.compat] (w : S) : Decidable (IsWorld F w) :=
  inferInstanceAs (Decidable (∀ x : S, F.compat w x → refines F w x))

/-! ### The ortholattice of regular propositions -/

/-- The regular propositions of `F` form the ortholattice of concepts of its orthogonality
    relation. -/
abbrev CompatFrame.Regular : Type _ := Concept S S F.ortho

variable {F}

/-- `F.regOf A h` is the regular proposition with underlying set `A`. -/
def CompatFrame.regOf (F : CompatFrame S) (A : Set S) (h : IsRegular F A) : F.Regular :=
  Concept.ofIsExtent F.ortho A ((isRegular_iff_isExtent F A).mp h)

theorem CompatFrame.Regular.isRegular (A : F.Regular) : IsRegular F A :=
  (isRegular_iff_isExtent F A).mpr A.isExtent_extent

@[simp] theorem CompatFrame.coe_regOf (A : Set S) (h : IsRegular F A) :
    (F.regOf A h : Set S) = A := rfl

@[simp] theorem CompatFrame.mem_regOf (A : Set S) (h : IsRegular F A) (x : S) :
    x ∈ F.regOf A h ↔ x ∈ A := Iff.rfl

@[simp] theorem CompatFrame.Regular.coe_inf (A B : F.Regular) :
    ((A ⊓ B : F.Regular) : Set S) = (A : Set S) ∩ (B : Set S) := rfl

@[simp] theorem CompatFrame.Regular.coe_top :
    ((⊤ : F.Regular) : Set S) = Set.univ := rfl

@[simp] theorem CompatFrame.Regular.coe_bot :
    ((⊥ : F.Regular) : Set S) = ∅ := Concept.extent_bot_eq_empty F.ortho

@[simp] theorem CompatFrame.Regular.coe_eq_empty {A : F.Regular} : (A : Set S) = ∅ ↔ A = ⊥ := by
  rw [← coe_bot, SetLike.coe_set_eq]

@[simp] theorem CompatFrame.Regular.coe_compl (A : F.Regular) :
    ((Aᶜ : F.Regular) : Set S) = orthoNeg F (A : Set S) := by
  show (Aᶜ).extent = orthoNeg F A.extent
  rw [orthoNeg_eq_upperPolar, Concept.extent_compl, ← Concept.upperPolar_extent]

@[simp] theorem CompatFrame.Regular.coe_sup (A B : F.Regular) :
    ((A ⊔ B : F.Regular) : Set S) = disj F (A : Set S) (B : Set S) := by
  rw [← InvolutiveCompl.compl_compl (A ⊔ B), InvolutiveCompl.compl_sup]
  simp only [coe_compl, coe_inf, disj]

@[simp] theorem CompatFrame.Regular.coe_iInf {ι : Sort*} (f : ι → F.Regular) :
    ((⨅ i, f i : F.Regular) : Set S) = ⋂ i, (f i : Set S) :=
  Concept.extent_iInf f

/-- An arbitrary join of regular propositions is the De Morgan disjunction `¬⋂ᵢ ¬Aᵢ`. -/
@[simp] theorem CompatFrame.Regular.coe_iSup {ι : Sort*} (f : ι → F.Regular) :
    ((⨆ i, f i : F.Regular) : Set S) = orthoNeg F (⋂ i, orthoNeg F (f i : Set S)) := by
  show (⨆ i, f i).extent = _
  simp only [Concept.extent_iSup, ← Concept.upperPolar_extent, ← upperPolar_eq_lowerPolar,
    ← orthoNeg_eq_upperPolar]
  rfl

end Orthologic
