module

public import Linglib.Semantics.Quantifier.Defs
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.UpperLower.Closure

/-!
# Monotone determiner denotations

A determiner denotation is scope monotone when enlarging the scope preserves it, and restrictor
monotone when enlarging the restrictor does. This file proves the facts about these and the
related monotonicities that need only the order on sets.

Outer negation reverses a monotonicity and so does inner negation, so the dual of a monotone
quantifier is monotone. A determiner denotation is restrictor monotone if and only if it is
monotone under each of Peters and Westerståhl's two ways of enlarging the restrictor, by members
of the scope and by non-members. The scope monotonicities are closed under meet and join. A
quantifier is a meet of two quantifiers, each monotone or antitone, if and only if its set of
scopes is order-connected.

## Main results

* `Quantifier.Det.scopeMonotone_iff_isUpperSet`: a determiner denotation is scope monotone if and
  only if each of its sets of scopes is an upper set.
* `Quantifier.Det.restrictorMonotone_iff_upSW_and_upSE`: a determiner denotation is restrictor
  monotone if and only if it is ↑SW and ↑SE monotone.
* `Quantifier.ordConnected_setOf_iff_exists_eq_inf`: a quantifier is a meet of two quantifiers, each
  monotone or antitone, if and only if its set of scopes is order-connected.

## References

* [barwise-cooper-1981]
* [peters-westerstahl-2006]
* [van-benthem-1984]
-/

public section

namespace Quantifier

variable {α : Type*}

theorem individual_monotone (a : α) : Monotone (individual a) := fun _ _ h ha ↦ h ha

theorem individual_inter {a : α} {B B' : Set α} :
    individual a (B ∩ B') ↔ individual a B ∧ individual a B' :=
  Iff.rfl

/-- A quantifier is the meet of two quantifiers, each monotone or antitone, exactly when its
scopes are order-connected: with any two scopes it has every scope between them. -/
theorem ordConnected_setOf_iff_exists_eq_inf {Q : Quantifier α} :
    {B | Q B}.OrdConnected ↔ ∃ Q₁ Q₂ : Quantifier α, (Monotone Q₁ ∨ Antitone Q₁) ∧
      (Monotone Q₂ ∨ Antitone Q₂) ∧ Q = Q₁ ⊓ Q₂ := by
  refine ⟨fun h ↦ ⟨(· ∈ upperClosure {B | Q B}), (· ∈ lowerClosure {B | Q B}),
    .inl fun _ _ hBC hB ↦ (upperClosure _).upper hBC hB,
    .inr fun _ _ hBC hB ↦ (lowerClosure _).lower hBC hB,
    funext fun B ↦ congrArg (B ∈ ·) h.upperClosure_inter_lowerClosure.symm⟩, ?_⟩
  rintro ⟨Q₁, Q₂, h₁, h₂, rfl⟩
  have key {Q' : Quantifier α} (h : Monotone Q' ∨ Antitone Q') : {B | Q' B}.OrdConnected :=
    h.elim (fun hm ↦ (isUpperSet_setOfPred.2 hm).ordConnected)
      fun ha ↦ (isLowerSet_setOfPred.2 ha).ordConnected
  exact (key h₁).inter (key h₂)

namespace Det

variable {d d' : Det α} {A B : Set α}

/-! ### The negations -/

theorem ScopeMonotone.compl (h : d.ScopeMonotone) : dᶜ.ScopeAntitone :=
  fun A _ _ hB hn hd ↦ hn (h A hB hd)

theorem ScopeAntitone.compl (h : d.ScopeAntitone) : dᶜ.ScopeMonotone :=
  fun A _ _ hB hn hd ↦ hn (h A hB hd)

theorem ScopeMonotone.innerNeg (h : d.ScopeMonotone) : d.innerNeg.ScopeAntitone :=
  fun A _ _ hB ↦ h A (Set.compl_subset_compl.2 hB)

theorem ScopeAntitone.innerNeg (h : d.ScopeAntitone) : d.innerNeg.ScopeMonotone :=
  fun A _ _ hB ↦ h A (Set.compl_subset_compl.2 hB)

theorem RestrictorMonotone.compl (h : d.RestrictorMonotone) : dᶜ.RestrictorAntitone :=
  fun B _ _ hA hn hd ↦ hn (h B hA hd)

theorem RestrictorAntitone.compl (h : d.RestrictorAntitone) : dᶜ.RestrictorMonotone :=
  fun B _ _ hA hn hd ↦ hn (h B hA hd)

@[simp] theorem innerNeg_innerNeg (d : Det α) : d.innerNeg.innerNeg = d := by
  funext A B; simp [innerNeg]

@[simp] theorem dual_dual (d : Det α) : d.dual.dual = d := by
  funext A B; simp [dual, innerNeg]

theorem innerNeg_compl (d : Det α) : dᶜ.innerNeg = d.innerNegᶜ := rfl

/-- A determiner denotation is scope antitone exactly when its inner negation is scope
monotone. -/
theorem scopeAntitone_iff_innerNeg : d.ScopeAntitone ↔ d.innerNeg.ScopeMonotone :=
  ⟨ScopeAntitone.innerNeg, fun h ↦ by simpa using h.innerNeg⟩

/-- A determiner denotation is scope monotone exactly when each of its sections is an upper set of
scopes. -/
theorem scopeMonotone_iff_isUpperSet : d.ScopeMonotone ↔ ∀ A, IsUpperSet {B | d A B} :=
  forall_congr' fun _ ↦ isUpperSet_setOfPred.symm

/-! ### Left monotonicity and smoothness -/

theorem RestrictorMonotone.upSE (h : d.RestrictorMonotone) : d.UpSEMon :=
  fun _ B _ hA _ ↦ h B hA

theorem RestrictorMonotone.upSW (h : d.RestrictorMonotone) : d.UpSWMon :=
  fun _ B _ hA _ ↦ h B hA

theorem RestrictorAntitone.downNW (h : d.RestrictorAntitone) : d.DownNWMon :=
  fun _ B _ hA _ ↦ h B hA

theorem RestrictorAntitone.downNE (h : d.RestrictorAntitone) : d.DownNEMon :=
  fun _ B _ hA _ ↦ h B hA

/-- A determiner denotation is restrictor monotone exactly when it is ↑SW and ↑SE monotone. -/
theorem restrictorMonotone_iff_upSW_and_upSE :
    d.RestrictorMonotone ↔ d.UpSWMon ∧ d.UpSEMon := by
  refine ⟨fun h ↦ ⟨h.upSW, h.upSE⟩, fun ⟨hSW, hSE⟩ B A A' hA hd ↦ ?_⟩
  refine hSE (A ∪ A' \ B) B A' (Set.union_subset hA Set.sdiff_subset) Set.subset_union_right
    (hSW A B _ Set.subset_union_left ?_ hd)
  rintro x ⟨hx | hx, hB⟩
  exacts [hx, absurd hB hx.2]

/-- A determiner denotation is restrictor antitone exactly when it is ↓NW and ↓NE monotone. -/
theorem restrictorAntitone_iff_downNW_and_downNE :
    d.RestrictorAntitone ↔ d.DownNWMon ∧ d.DownNEMon := by
  refine ⟨fun h ↦ ⟨h.downNW, h.downNE⟩, fun ⟨hNW, hNE⟩ B A A' hA hd ↦ ?_⟩
  refine hNW (A ∪ A' ∩ B) B A Set.subset_union_left ?_
    (hNE A' B _ (Set.union_subset hA Set.inter_subset_left) Set.subset_union_right hd)
  rintro x ⟨hx | hx, hB⟩
  exacts [hx, absurd hx.2 hB]

theorem UpSEMon.compl (h : d.UpSEMon) : dᶜ.DownNWMon :=
  fun A B A' h₁ h₂ hn hd ↦ hn (h A' B A h₁ h₂ hd)

theorem DownNWMon.compl (h : d.DownNWMon) : dᶜ.UpSEMon :=
  fun A B A' h₁ h₂ hn hd ↦ hn (h A' B A h₁ h₂ hd)

theorem UpSWMon.compl (h : d.UpSWMon) : dᶜ.DownNEMon :=
  fun A B A' h₁ h₂ hn hd ↦ hn (h A' B A h₁ h₂ hd)

theorem DownNEMon.compl (h : d.DownNEMon) : dᶜ.UpSWMon :=
  fun A B A' h₁ h₂ hn hd ↦ hn (h A' B A h₁ h₂ hd)

theorem DownNEMon.innerNeg (h : d.DownNEMon) : d.innerNeg.DownNWMon :=
  fun A B A' h₁ h₂ ↦ h A Bᶜ A' h₁ h₂

theorem DownNWMon.innerNeg (h : d.DownNWMon) : d.innerNeg.DownNEMon :=
  fun A B A' h₁ h₂ ↦ h A Bᶜ A' h₁ (by rwa [Set.sdiff_compl])

theorem UpSEMon.innerNeg (h : d.UpSEMon) : d.innerNeg.UpSWMon :=
  fun A B A' h₁ h₂ ↦ h A Bᶜ A' h₁ (by rwa [Set.sdiff_compl])

theorem UpSWMon.innerNeg (h : d.UpSWMon) : d.innerNeg.UpSEMon :=
  fun A B A' h₁ h₂ ↦ h A Bᶜ A' h₁ h₂

theorem smooth_iff_coSmooth_compl : d.Smooth ↔ dᶜ.CoSmooth :=
  ⟨fun ⟨hNE, hSE⟩ ↦ ⟨hSE.compl, hNE.compl⟩,
    fun ⟨hNW, hSW⟩ ↦ ⟨by simpa using hSW.compl, by simpa using hNW.compl⟩⟩

theorem smooth_iff_coSmooth_innerNeg : d.Smooth ↔ d.innerNeg.CoSmooth :=
  ⟨fun ⟨hNE, hSE⟩ ↦ ⟨hNE.innerNeg, hSE.innerNeg⟩,
    fun ⟨hNW, hSW⟩ ↦ ⟨by simpa using hNW.innerNeg, by simpa using hSW.innerNeg⟩⟩

/-! ### Meets, joins and restriction -/

theorem ScopeMonotone.inf (h : d.ScopeMonotone) (h' : d'.ScopeMonotone) :
    (d ⊓ d').ScopeMonotone :=
  fun A _ _ hB hd ↦ ⟨h A hB hd.1, h' A hB hd.2⟩

theorem ScopeAntitone.inf (h : d.ScopeAntitone) (h' : d'.ScopeAntitone) :
    (d ⊓ d').ScopeAntitone :=
  fun A _ _ hB hd ↦ ⟨h A hB hd.1, h' A hB hd.2⟩

theorem ScopeMonotone.sup (h : d.ScopeMonotone) (h' : d'.ScopeMonotone) :
    (d ⊔ d').ScopeMonotone :=
  fun A _ _ hB hd ↦ hd.imp (h A hB) (h' A hB)

theorem ScopeAntitone.sup (h : d.ScopeAntitone) (h' : d'.ScopeAntitone) :
    (d ⊔ d').ScopeAntitone :=
  fun A _ _ hB hd ↦ hd.imp (h A hB) (h' A hB)

theorem ScopeMonotone.adjRestrict (h : d.ScopeMonotone) (C : Set α) :
    (d.adjRestrict C).ScopeMonotone :=
  fun A ↦ h (A ∩ C)

theorem ScopeAntitone.adjRestrict (h : d.ScopeAntitone) (C : Set α) :
    (d.adjRestrict C).ScopeAntitone :=
  fun A ↦ h (A ∩ C)

/-! ### Right continuity -/

theorem ScopeMonotone.rightContinuous (h : d.ScopeMonotone) : d.RightContinuous :=
  fun A ↦ (isUpperSet_setOfPred.2 (h A)).ordConnected

theorem ScopeAntitone.rightContinuous (h : d.ScopeAntitone) : d.RightContinuous :=
  fun A ↦ (isLowerSet_setOfPred.2 (h A)).ordConnected

end Det

end Quantifier
