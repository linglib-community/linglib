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
reflexive, symmetric compatibility relation, and a possibility can settle a disjunction without
settling either disjunct. The propositions are the *regular* sets, negation is the orthocomplement
`orthoNeg`, and the regular sets form an ortholattice that need not be Boolean.

## Main definitions

* `CompatFrame`: a set of possibilities with a reflexive, symmetric compatibility relation.
* `orthoNeg`, `disj`: orthocomplement negation and De Morgan disjunction.
* `IsRegular`, `refines`, `IsWorld`: regularity, refinement, and worlds.
* `regularClosure`: the closure operator whose fixed points are the regular sets.
* `CompatFrame.Regular`: the ortholattice of regular propositions.
* `identityFrame`: the frame whose compatibility is identity.

## Main results

* `IsRegular.mem_of_refines`: regular sets are closed under refinement.
* `refines_iff_mem_orthoNeg_orthoNeg`: the refinements of `x` form the regular set `¬¬{x}`.
* `isRegular_iff_isExtent`: the regular sets are the concept extents of orthogonality.
* `orthoNeg_classical`: negation is Boolean when compatibility is identity.

## Implementation notes

A frame also carries its orthogonality relation `ortho`, the complement of compatibility, which
defaults to `¬ compat` and is stored as data in the way `Preorder` stores `<`. The regular
propositions are the concepts of `ortho` (`Core/Order/Concept.lean`), and a frame built from an
orthogonality relation, such as the canonical frame of an ortholattice, keeps that relation
definitionally. Decidability of `compat` is not bundled: use sites take
`[DecidableRel F.compat]`, as for `SimpleGraph.Adj`. The paper's frames are nonempty; no result
here needs it, so the structure does not require it.

## References

* [holliday-mandelkern-2024]
-/

@[expose] public section

namespace Orthologic

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

/-! ### Orthocomplement negation and connectives -/

/-- The orthocomplement `¬A` holds at the possibilities compatible with no `A`-possibility,
    those whose information settles `¬A` ([holliday-mandelkern-2024] Proposition 4.8,
    eq. (1)). -/
def orthoNeg (F : CompatFrame S) (A : Set S) : Set S :=
  { x | ∀ y : S, F.compat x y → y ∉ A }

@[simp] theorem mem_orthoNeg (F : CompatFrame S) (A : Set S) (x : S) :
    x ∈ orthoNeg F A ↔ ∀ y : S, F.compat x y → y ∉ A := Iff.rfl

instance [Fintype S] (F : CompatFrame S) [DecidableRel F.compat]
    (A : Set S) [DecidablePred (· ∈ A)] (x : S) : Decidable (x ∈ orthoNeg F A) := by
  show Decidable (∀ y : S, F.compat x y → y ∉ A); infer_instance

/-- This instance decides `orthoNeg F A x` in application form from `[DecidablePred A]`, for
    goals that reduce membership. -/
instance orthoNeg_apply_decidable [Fintype S] (F : CompatFrame S)
    [DecidableRel F.compat] (A : Set S) [DecidablePred A] (x : S) :
    Decidable (orthoNeg F A x) := by
  show Decidable (∀ y : S, F.compat x y → y ∉ A)
  have : DecidablePred (· ∈ A) := inferInstanceAs (DecidablePred A)
  infer_instance

/-- Conjunction is intersection, named beside `disj`. -/
abbrev conj (A B : Set S) : Set S := A ∩ B

/-- The De Morgan disjunction `A ∨ B = ¬(¬A ∩ ¬B)` holds at `x` iff every possibility
    compatible with `x` is compatible with one making `A` or `B` true, so it is weaker than union
    ([holliday-mandelkern-2024] Proposition 4.8, eq. (2)). -/
def disj (F : CompatFrame S) (A B : Set S) : Set S :=
  orthoNeg F (orthoNeg F A ∩ orthoNeg F B)

instance [Fintype S] (F : CompatFrame S) [DecidableRel F.compat]
    (A B : Set S) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] (x : S) :
    Decidable (x ∈ disj F A B) := by
  unfold disj; infer_instance

instance disj_apply_decidable [Fintype S] (F : CompatFrame S)
    [DecidableRel F.compat] (A B : Set S) [DecidablePred A] [DecidablePred B]
    (x : S) : Decidable (disj F A B x) := by
  show Decidable (∀ y : S, F.compat x y → y ∉ orthoNeg F A ∩ orthoNeg F B)
  have hA : DecidablePred (· ∈ A) := inferInstanceAs (DecidablePred A)
  have hB : DecidablePred (· ∈ B) := inferInstanceAs (DecidablePred B)
  infer_instance

instance conj_apply_decidable (A B : Set S)
    [DecidablePred A] [DecidablePred B] (x : S) :
    Decidable (conj A B x) :=
  inferInstanceAs (Decidable (A x ∧ B x))

/-! ### Regularity -/

/-- A set `A` is regular when every possibility outside `A` is compatible with one all of whose
    compatible possibilities lie outside `A`; only regular sets count as propositions
    ([holliday-mandelkern-2024] Definition 4.3). -/
def IsRegular (F : CompatFrame S) (A : Set S) : Prop :=
  ∀ x : S, x ∈ A ∨ ∃ y : S, F.compat x y ∧ ∀ z : S, F.compat y z → z ∉ A

instance [Fintype S] (F : CompatFrame S) [DecidableRel F.compat]
    (A : Set S) [DecidablePred (· ∈ A)] : Decidable (IsRegular F A) := by
  unfold IsRegular; infer_instance

/-- This instance decides `IsRegular F A` from `[DecidablePred A]`. -/
instance isRegular_apply_decidable [Fintype S] (F : CompatFrame S)
    [DecidableRel F.compat] (A : Set S) [DecidablePred A] : Decidable (IsRegular F A) := by
  unfold IsRegular
  have : DecidablePred (· ∈ A) := inferInstanceAs (DecidablePred A)
  infer_instance

/-! ### Refinement and worlds -/

/-- A possibility `y` refines `x`, written `y ⊑ x`, when every possibility compatible with `y`
    is compatible with `x`, so that `y` carries at least as much information
    ([holliday-mandelkern-2024] Lemma 4.4, condition 2). -/
def refines (F : CompatFrame S) (y x : S) : Prop :=
  ∀ z : S, F.compat y z → F.compat x z

instance [Fintype S] (F : CompatFrame S) [DecidableRel F.compat]
    (y x : S) : Decidable (refines F y x) := by
  unfold refines; infer_instance

/-- Regular sets are closed under refinement ([holliday-mandelkern-2024] Lemma 4.4, one direction).
-/
theorem IsRegular.mem_of_refines {F : CompatFrame S} {A : Set S} (hA : IsRegular F A)
    {z x : S} (h : refines F z x) (hx : x ∈ A) : z ∈ A :=
  (hA z).resolve_right fun ⟨_, hzw, hw⟩ ↦ hw x (h _ hzw).symm hx

/-- The refinements of `x` are the possibilities settling `¬¬{x}`, so they form a regular set
    ([holliday-mandelkern-2024] Lemma 4.5). -/
theorem refines_iff_mem_orthoNeg_orthoNeg (F : CompatFrame S) {z x : S} :
    refines F z x ↔ z ∈ orthoNeg F (orthoNeg F {x}) := by
  simp only [refines, mem_orthoNeg, Set.mem_singleton_iff, not_forall, not_not, exists_prop,
    exists_eq_right]
  exact forall₂_congr fun _ _ ↦ ⟨CompatFrame.compat.symm, CompatFrame.compat.symm⟩

/-- A world is a possibility that refines everything it is compatible with, the most
    informative kind of possibility ([holliday-mandelkern-2024] Definition 4.6). -/
def IsWorld (F : CompatFrame S) (w : S) : Prop :=
  ∀ x : S, F.compat w x → refines F w x

instance [Fintype S] (F : CompatFrame S) [DecidableRel F.compat]
    (w : S) : Decidable (IsWorld F w) := by
  unfold IsWorld; infer_instance

/-! ### Classical collapse -/

/-- When compatibility is identity, orthocomplement is Boolean negation ([holliday-mandelkern-2024]
Remark 4.9). -/
theorem orthoNeg_classical
    (F : CompatFrame S)
    (hClassical : ∀ x y, F.compat x y → x = y)
    (A : Set S) (x : S) :
    x ∈ orthoNeg F A ↔ x ∉ A := by
  simp only [mem_orthoNeg]
  constructor
  · intro h hAx
    exact h x (F.refl x) hAx
  · intro hNotA y hcompat hAy
    have heq := hClassical x y hcompat
    subst heq; exact hNotA hAy

/-- In the identity frame each possibility is compatible only with itself. -/
def identityFrame [DecidableEq S] : CompatFrame S where
  compat := fun x y ↦ x = y
  compat_refl := ⟨fun _ ↦ rfl⟩
  compat_symm := ⟨fun _ _ h ↦ h.symm⟩

instance [DecidableEq S] :
    DecidableRel (identityFrame (S := S)).compat := fun a b ↦ by
  show Decidable (a = b); infer_instance

theorem identityFrame_classical [DecidableEq S]
    (A : Set S) (x : S) :
    x ∈ orthoNeg (identityFrame (S := S)) A ↔ x ∉ A :=
  orthoNeg_classical identityFrame (fun _ _ h ↦ h) A x

/-! ### The c_◇ closure operator -/

/-- The closure operator `c_◇` sends `A` to the possibilities all of whose compatible
    possibilities are compatible with an `A`-possibility; its fixed points are the regular sets
    ([holliday-mandelkern-2024] footnote 19). -/
def regularClosure (F : CompatFrame S) : ClosureOperator (Set S) where
  toFun A := { x | ∀ y, F.compat x y → ∃ z, F.compat y z ∧ z ∈ A }
  monotone' _ _ hAB _ hx y hy := by
    obtain ⟨z, hyz, hz⟩ := hx y hy; exact ⟨z, hyz, hAB hz⟩
  le_closure' _ x hx _ hy := ⟨x, hy.symm, hx⟩
  idempotent' A := by
    apply Set.eq_of_subset_of_subset
    · intro x hx y hy
      obtain ⟨z, hyz, hz⟩ := hx y hy
      have hzy : F.compat z y := hyz.symm
      obtain ⟨w, hyw, hwA⟩ := hz y hzy
      exact ⟨w, hyw, hwA⟩
    · intro x hx y hy
      obtain ⟨z, hyz, hz⟩ := hx y hy
      exact ⟨z, hyz, fun y' hy' ↦ ⟨z, hy'.symm, hz⟩⟩
  IsClosed A := IsRegular F A
  isClosed_iff {A} := by
    constructor
    · -- IsRegular F A → c_◇(A) = A
      intro hReg
      apply Set.eq_of_subset_of_subset
      · intro x hx
        rcases hReg x with hxA | ⟨y, hxy, hy⟩
        · exact hxA
        · exfalso
          obtain ⟨z, hyz, hzA⟩ := hx y hxy
          exact hy z hyz hzA
      · intro x hx _ hy
        exact ⟨x, hy.symm, hx⟩
    · -- c_◇(A) = A → IsRegular F A
      intro hEq x
      by_cases h : x ∈ A
      · exact Or.inl h
      · right
        -- x ∉ A = c_◇(A), so ¬(∀ y ◇ x, ∃ z ◇ y, z ∈ A)
        have hNot : ¬ ∀ y, F.compat x y → ∃ z, F.compat y z ∧ z ∈ A := by
          intro habs
          apply h
          rw [← hEq]
          exact habs
        push Not at hNot
        obtain ⟨y, hxy, hy⟩ := hNot
        exact ⟨y, hxy, hy⟩

@[simp] theorem mem_regularClosure (F : CompatFrame S) (A : Set S) (x : S) :
    x ∈ regularClosure F A ↔ ∀ y, F.compat x y → ∃ z, F.compat y z ∧ z ∈ A :=
  Iff.rfl

theorem regularClosure_isClosed_iff_isRegular (F : CompatFrame S) (A : Set S) :
    (regularClosure F).IsClosed A ↔ IsRegular F A := Iff.rfl

/-! ### Closure properties of regular sets -/

theorem orthoNeg_isRegular (F : CompatFrame S) (A : Set S) :
    IsRegular F (orthoNeg F A) := by
  intro x
  by_cases h : x ∈ orthoNeg F A
  · exact Or.inl h
  · right
    rw [mem_orthoNeg] at h
    push Not at h
    obtain ⟨y, hxy, hyA⟩ := h
    refine ⟨y, hxy, fun z hyz hzN ↦ ?_⟩
    rw [mem_orthoNeg] at hzN
    exact hzN y (hyz.symm) hyA

theorem inter_isRegular {F : CompatFrame S} {A B : Set S}
    (hA : IsRegular F A) (hB : IsRegular F B) : IsRegular F (A ∩ B) := by
  intro x
  by_cases h : x ∈ A ∩ B
  · exact Or.inl h
  · right
    rw [Set.mem_inter_iff, not_and_or] at h
    rcases h with hxA | hxB
    · rcases hA x with hAx | ⟨y, hxy, hy⟩
      · exact absurd hAx hxA
      · exact ⟨y, hxy, fun z hyz hz ↦ hy z hyz hz.1⟩
    · rcases hB x with hBx | ⟨y, hxy, hy⟩
      · exact absurd hBx hxB
      · exact ⟨y, hxy, fun z hyz hz ↦ hy z hyz hz.2⟩

theorem disj_isRegular (F : CompatFrame S) (A B : Set S) :
    IsRegular F (disj F A B) :=
  orthoNeg_isRegular F _

theorem empty_isRegular (F : CompatFrame S) : IsRegular F (∅ : Set S) := by
  intro x
  exact Or.inr ⟨x, F.refl x, fun _ _ h ↦ h.elim⟩

theorem univ_isRegular (F : CompatFrame S) : IsRegular F (Set.univ : Set S) :=
  fun _ ↦ Or.inl trivial

/-- Orthocomplementation is involutive on regular sets, `¬¬A = A`
    ([holliday-mandelkern-2024] Proposition 4.8). -/
theorem orthoNeg_orthoNeg_of_isRegular (F : CompatFrame S) {A : Set S}
    (hA : IsRegular F A) : orthoNeg F (orthoNeg F A) = A := by
  apply Set.eq_of_subset_of_subset
  · intro x hx
    rcases hA x with hxA | ⟨y, hxy, hy⟩
    · exact hxA
    · exfalso
      rw [mem_orthoNeg] at hx
      have hyN : ¬ y ∈ orthoNeg F A := hx y hxy
      rw [mem_orthoNeg] at hyN
      push Not at hyN
      obtain ⟨z, hyz, hzA⟩ := hyN
      exact hy z hyz hzA
  · intro x hxA
    rw [mem_orthoNeg]
    intro y hxy
    rw [mem_orthoNeg]
    push Not
    exact ⟨x, hxy.symm, hxA⟩

/-! ### Regular sets as concept extents -/

open Order

theorem orthoNeg_eq_upperPolar (F : CompatFrame S) (A : Set S) :
    orthoNeg F A = upperPolar F.ortho A := by
  ext x
  exact ⟨fun hx a ha ↦ (F.ortho_iff a x).mpr fun hc ↦ hx a hc.symm ha,
    fun hx y hxy hyA ↦ (F.ortho_iff y x).mp (hx hyA) hxy.symm⟩

theorem isRegular_iff_orthoNeg_orthoNeg (F : CompatFrame S) (A : Set S) :
    IsRegular F A ↔ orthoNeg F (orthoNeg F A) = A :=
  ⟨orthoNeg_orthoNeg_of_isRegular F, fun h ↦ h ▸ orthoNeg_isRegular F _⟩

/-- The regular sets of `F` are exactly the concept extents of its orthogonality relation.
    [holliday-mandelkern-2024]'s Proposition 4.8 is then mathlib's
    `upperPolar_lowerPolar_upperPolar`. -/
theorem isRegular_iff_isExtent (F : CompatFrame S) (A : Set S) :
    IsRegular F A ↔ IsExtent F.ortho A := by
  rw [isRegular_iff_orthoNeg_orthoNeg, isExtent_iff, orthoNeg_eq_upperPolar,
    orthoNeg_eq_upperPolar, upperPolar_eq_lowerPolar F.ortho]

/-! ### The ortholattice of regular propositions -/

/-- The regular propositions of `F` form the ortholattice of concepts of its orthogonality
    relation. -/
abbrev CompatFrame.Regular (F : CompatFrame S) : Type _ := Concept S S F.ortho

variable {F : CompatFrame S}

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

end Orthologic
