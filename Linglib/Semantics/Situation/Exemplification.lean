module

public import Linglib.Core.Logic.Function.DependsOn
public import Linglib.Core.Order.UpperLower.Closure
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Topology.DerivedSet
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Order.UpperLowerSetTopology

/-!
# Exemplification

This file defines exemplification, a relation between a set in a topological space and a point:
`x` exemplifies `p` if `x` is an interior point or an isolated point of `p`.

The intended spaces are the situations of a situation semantics, ordered by parthood, with the
lower set topology. There `x` exemplifies `p` iff every part of `x` is in `p` or `x` is a minimal
member of `p`: the situation `x` contains nothing that does not contribute to the truth of the
proposition `p`.

## Main definitions

* `Situation.Exemplifies`: `x` exemplifies `p` if `x` is an interior point or an isolated point
  of `p`.

## Main statements

* `Situation.exemplifies_congr`: whether `x` exemplifies `p` depends only on the germ of `p` at
  `x`.
* `Situation.exemplifies_iff`: in the lower set topology of a partial order, `x` exemplifies `p`
  iff every part of `x` is in `p` or `x` is a minimal member of `p`.
* `Situation.closure_setOf_exemplifies`: in a well-founded order, a closed set is the closure of
  its exemplifiers.
* `Situation.setOf_exemplifies_eq`: the exemplifiers of a proposition are the situations all of
  whose parts are in it together with its minimal members.
* `Situation.minimal_mem_iff_maximal_isIrreducible`: the minimal members of a closed set are the
  generic points of its irreducible components.

## Implementation notes

The characterization `Situation.exemplifies_iff` is the definition of [kratzer-2012]. The
conjunctive form of [deigan-2020] and [bondarenko-2022] is `Situation.exemplifies_iff_mem_and`.
Both need a partial order: in a preorder an isolated point need not be minimal.

Of the two sets whose union is the exemplifiers of a proposition, the first is homogeneous, closed
under parthood, and the second quantized, an antichain. Their union need be neither.

The set is the first argument, as the predicate is the first argument of `Minimal`, so that
`Exemplifies p` is the predicate of exemplifying `p`.

## References

* [kratzer-2012]
* [kratzer-2023]
* [deigan-2020]
* [bondarenko-2022]
-/

@[expose] public section

open Set Topology

namespace Situation

variable {α : Type*} [TopologicalSpace α]

/-! ### Topological spaces -/

section TopologicalSpace

variable {p q : Set α} {x : α}

/-- `x` exemplifies `p` if `x` is an interior point or an isolated point of `p`. -/
def Exemplifies (p : Set α) (x : α) : Prop :=
  x ∈ interior p ∨ x ∈ p \ derivedSet p

theorem Exemplifies.mem (h : Exemplifies p x) : x ∈ p :=
  h.elim (fun h ↦ interior_subset h) fun h ↦ h.1

theorem _root_.IsOpen.exemplifies_iff (hp : IsOpen p) : Exemplifies p x ↔ x ∈ p :=
  ⟨Exemplifies.mem, fun h ↦ .inl (hp.interior_eq.symm ▸ h)⟩

theorem Exemplifies.inter (hp : Exemplifies p x) (hq : Exemplifies q x) :
    Exemplifies (p ∩ q) x := by
  by_cases h : x ∈ derivedSet (p ∩ q)
  · rw [Exemplifies, interior_inter]
    exact .inl ⟨hp.resolve_right fun h' ↦ h'.2 (derivedSet_mono _ _ inter_subset_left h),
      hq.resolve_right fun h' ↦ h'.2 (derivedSet_mono _ _ inter_subset_right h)⟩
  · exact .inr ⟨⟨hp.mem, hq.mem⟩, h⟩

/-- Whether `x` exemplifies `p` depends only on the germ of `p` at `x`. -/
theorem exemplifies_congr (h : p =ᶠ[𝓝 x] q) : Exemplifies p x ↔ Exemplifies q x := by
  have h' := Filter.eventuallyEqSet_iff.1 h
  simp only [Exemplifies, mem_interior_iff_mem_nhds, mem_sdiff, mem_derivedSet,
    accPt_iff_frequently]
  exact or_congr (Filter.eventually_congr h') (and_congr h'.self_of_nhds
    (not_congr (Filter.frequently_congr (h'.mono fun _ hy ↦ and_congr_right fun _ ↦ hy))))

end TopologicalSpace

/-! ### Part orders -/

section PartialOrder

variable [PartialOrder α] [Topology.IsLowerSet α] {p s : Set α} {x y z : α}

open Topology.IsLowerSet

/-- In the lower set topology of a partial order, `x` exemplifies `p` iff every part of `x` is in
`p` or `x` is a minimal member of `p`. -/
theorem exemplifies_iff : Exemplifies p x ↔ Iic x ⊆ p ∨ Minimal (· ∈ p) x := by
  simp only [Exemplifies, mem_interior_iff_mem_nhds, mem_sdiff, mem_derivedSet,
    accPt_iff_frequently, nhds_eq_principal_Iic, Filter.mem_principal,
    Filter.frequently_principal, minimal_iff_forall_lt]
  exact or_congr_right (and_congr_right fun _ ↦
    ⟨fun h y hy hyp ↦ h ⟨y, hy.le, hy.ne, hyp⟩,
      fun h ⟨y, hyx, hne, hyp⟩ ↦ h (lt_of_le_of_ne hyx hne) hyp⟩)

instance [Fintype α] [DecidableLE α] [DecidablePred (· ∈ p)] : DecidablePred (Exemplifies p) :=
  fun x ↦ decidable_of_iff ((∀ y ≤ x, y ∈ p) ∨ x ∈ p ∧ ∀ y ∈ p, y ≤ x → x ≤ y)
    exemplifies_iff.symm

theorem exemplifies_iff_mem_and :
    Exemplifies p x ↔ x ∈ p ∧ ((∀ y < x, y ∈ p) ∨ ∀ y < x, y ∉ p) := by
  rw [exemplifies_iff, minimal_iff_forall_lt, and_or_left]
  refine or_congr ⟨fun h ↦ ⟨h self_mem_Iic, fun y hy ↦ h hy.le⟩, fun h y hy ↦ ?_⟩ .rfl
  obtain rfl | hlt := (mem_Iic.1 hy).eq_or_lt
  exacts [h.1, h.2 y hlt]

theorem _root_.Minimal.exemplifies (h : Minimal (· ∈ p) x) : Exemplifies p x :=
  exemplifies_iff.2 (.inr h)

theorem _root_.IsAntichain.exemplifies_iff (hp : IsAntichain (· ≤ ·) p) :
    Exemplifies p x ↔ x ∈ p :=
  ⟨Exemplifies.mem, fun hx ↦ Minimal.exemplifies ⟨hx, fun y hy hyx ↦ by
    obtain rfl | hne := eq_or_ne y x
    exacts [le_rfl, absurd hyx (hp hy hx hne)]⟩⟩

/-- Whether `x` exemplifies `p` depends only on the members of `p` among the parts of `x`. -/
theorem dependsOn_exemplifies_Iic (x : α) : Set.DependsOn (Exemplifies · x) (Iic x) :=
  fun _ ↦ propext <| exemplifies_congr <| Filter.eventuallyEqSet_iff.2 <| by
    rw [nhds_eq_principal_Iic, Filter.eventually_principal]
    exact fun _ hy ↦ and_iff_right hy

/-- If `x` has a proper part in `p` and a part outside `p`, then `x` does not exemplify `p`. -/
theorem not_exemplifies_of_lt (hy : y < x) (hyp : y ∈ p) (hz : z ≤ x) (hzp : z ∉ p) :
    ¬ Exemplifies p x :=
  fun h ↦ (exemplifies_iff.1 h).elim (fun hs ↦ hzp (hs hz)) fun hm ↦ hm.not_prop_of_lt hy hyp

/-! ### Homogeneous and quantized exemplifiers -/

omit [TopologicalSpace α] [Topology.IsLowerSet α] in
/-- The situations all of whose parts are in `p` are closed under parthood. -/
theorem isLowerSet_setOf_Iic_subset (p : Set α) : IsLowerSet {x | Iic x ⊆ p} :=
  fun _ _ hyx hx ↦ (Iic_subset_Iic.2 hyx).trans hx

/-- A part of a situation all of whose parts are in `p` exemplifies `p`. -/
theorem exemplifies_of_Iic_subset (h : Iic x ⊆ p) (hyx : y ≤ x) : Exemplifies p y :=
  exemplifies_iff.2 (.inl ((Iic_subset_Iic.2 hyx).trans h))

/-- The exemplifiers of a proposition are the situations all of whose parts are in it, which are
closed under parthood, together with its minimal members, no one of which is part of another. -/
theorem setOf_exemplifies_eq :
    {x | Exemplifies p x} = {x | Iic x ⊆ p} ∪ {x | Minimal (· ∈ p) x} :=
  Set.ext fun _ ↦ exemplifies_iff

/-! ### Closures -/

/-- `x` exemplifies the upper closure of `s` iff every part of `x` is in the upper closure or `x` is
a minimal member of `s`. -/
theorem exemplifies_upperClosure_iff :
    Exemplifies (upperClosure s : Set α) x ↔
      Iic x ⊆ upperClosure s ∨ Minimal (· ∈ s) x := by
  rw [exemplifies_iff]
  exact or_congr_right minimal_mem_upperClosure_iff

/-- If no member of an antichain `s` is minimal, then the exemplifiers of the upper closure of `s`
are the members of `s`. -/
theorem _root_.IsAntichain.exemplifies_upperClosure_iff (hs : IsAntichain (· ≤ ·) s)
    (hmin : ∀ a ∈ s, ¬ IsMin a) : Exemplifies (upperClosure s : Set α) x ↔ x ∈ s := by
  rw [Situation.exemplifies_upperClosure_iff]
  refine ⟨fun h ↦ h.elim (fun hsub ↦ ?_) fun h ↦ h.prop, fun h ↦ .inr ⟨h, fun y hy hyx ↦ ?_⟩⟩
  · obtain ⟨a, ha, hax⟩ := hsub self_mem_Iic
    obtain ⟨b, hba⟩ := not_isMin_iff.1 (hmin a ha)
    obtain ⟨c, hc, hcb⟩ := hsub (hba.le.trans hax)
    exact absurd (hcb.trans hba.le) (hs hc ha (hcb.trans_lt hba).ne)
  · obtain rfl | hne := eq_or_ne y x
    exacts [le_rfl, absurd hyx (hs hy h hne)]

/-- In a well-founded order, a closed set is the closure of its exemplifiers. -/
theorem closure_setOf_exemplifies [WellFoundedLT α] (hp : IsClosed p) :
    closure {x | Exemplifies p x} = p := by
  have hsub : {x | Exemplifies p x} ⊆ p := fun _ h ↦ Exemplifies.mem h
  refine (closure_minimal hsub hp).antisymm fun x hx ↦ ?_
  obtain ⟨m, hmx, hm⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ p) x hx
  rw [closure_eq_upperClosure]
  exact ⟨m, hm.exemplifies, hmx⟩

/-- The minimal members of a closed set `p` are the generic points of its irreducible components:
`x` is a minimal member of `p` iff the closure of `x` is a maximal irreducible subset of `p`. -/
theorem minimal_mem_iff_maximal_isIrreducible (hp : IsClosed p) :
    Minimal (· ∈ p) x ↔ Maximal (fun s : Set α ↦ IsIrreducible s ∧ s ⊆ p) (closure {x}) := by
  have hup := isClosed_iff_isUpper.1 hp
  have hirr (y : α) : IsIrreducible (Ici y) := IsLowerSet.closure_singleton (a := y) ▸
    isIrreducible_singleton.closure
  rw [IsLowerSet.closure_singleton]
  refine ⟨fun hx ↦ ⟨⟨hirr x, fun y hy ↦ hup hy hx.prop⟩, fun F ⟨hF, hFp⟩ hxF y hy ↦ ?_⟩,
    fun hx ↦ ⟨hx.prop.2 self_mem_Ici, fun z hz hzx ↦ ?_⟩⟩
  · obtain ⟨z, hzF, hzx, hzy⟩ := hF.2 (Iic x) (Iic y) (isOpen_iff_isLowerSet.2 (.Iic x))
      (isOpen_iff_isLowerSet.2 (.Iic y)) ⟨x, hxF self_mem_Ici, le_rfl⟩ ⟨y, hy, le_rfl⟩
    exact hx.eq_of_le (hFp hzF) hzx ▸ hzy
  · exact hx.le_of_ge ⟨hirr z, fun y hy ↦ hup hy hz⟩ (Ici_subset_Ici.2 hzx) self_mem_Ici

end PartialOrder

/-- If `y ∈ p`, `z ∉ p` and `z` is not part of `y`, then `y ⊔ z` does not exemplify `p`. -/
theorem not_exemplifies_sup [SemilatticeSup α] [Topology.IsLowerSet α] {p : Set α} {y z : α}
    (hy : y ∈ p) (hz : z ∉ p) (hzy : ¬ z ≤ y) : ¬ Exemplifies p (y ⊔ z) :=
  not_exemplifies_of_lt (left_lt_sup.2 hzy) hy le_sup_right hz

end Situation
