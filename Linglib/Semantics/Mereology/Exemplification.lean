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

In a situation semantics a proposition is a set of situations, and the situations are ordered by
parthood. A situation in which a proposition is true may contain much that has nothing to do
with its truth, and a situation exemplifies the proposition when it contains nothing of that
kind. The situations carry the topology whose open sets are the sets closed under parts. Its
closed sets are the persistent propositions, the closure of a set is the set of situations with a
part in it, and the least neighbourhood of a situation is the set of its parts.

For a set `p` in a topological space, we say that `x` *exemplifies* `p` when `x` is an interior
point or an isolated point of `p`. Whether `x` exemplifies `p` depends only on `p` near `x`, every
point of an open set exemplifies it, and a set has no exemplifier exactly when it has empty
interior and no isolated point.

In the topology of a part order the interior points of `p` are the points all of whose parts are
in `p` and the isolated points are the minimal elements of `p`. So `x` exemplifies `p` when every
part of `x` is in `p` or `x` is a minimal member of `p`, as a situation that is all mud exemplifies
the proposition that there is mud and a situation with three teapots and nothing else the
proposition that there are three teapots. Equivalently `x` is a member of `p` whose proper parts
are all members or all non-members. The exemplifiers of the closure of `s` are its interior
points and the minimal elements of `s`. In a well-founded part order a closed set is the closure
of its exemplifiers, and the closures of its minimal members are its irreducible components.

## Main definitions

* `Mereology.Exemplifies p x`: `x` is an interior point or an isolated point of `p`.

## Main results

* `Mereology.exemplifies_congr`: exemplification by `x` depends only on the germ of the set at
  `x`, so only on a neighbourhood of `x`, `Mereology.dependsOn_exemplifies`, and in a part order
  only on the parts of `x`, `Mereology.dependsOn_exemplifies_Iic`.
* `Mereology.forall_not_exemplifies_iff`: a set has no exemplifier iff it has empty interior and
  no isolated point.
* `Mereology.exemplifies_iff`: in a part order, `x` exemplifies `p` iff every part of `x` is in
  `p` or `x` is a minimal member of `p`.
* `Mereology.exemplifies_iff_mem_and`: `x` exemplifies `p` iff `x` is a member of `p` whose
  proper parts are all members or all non-members.
* `Mereology.exemplifies_upperClosure_iff`: the exemplifiers of the closure of `s` are its
  interior points and the minimal elements of `s`.
* `Mereology.closure_setOf_exemplifies`: in a well-founded part order a closed set is the
  closure of its exemplifiers.
* `Mereology.minimal_mem_iff_maximal_isIrreducible`: the minimal members of a closed set are the
  generic points of its irreducible components.

## Implementation notes

The disjunction over the parts of `x` is the definition of [kratzer-2012], and the conjunctive
form is that of [deigan-2020], which [bondarenko-2022] states for arbitrary individuals and sets
of them. Both are stated here for the lower set topology of a partial order, in which a point's
least neighbourhood is the set of its parts; in a preorder an isolated point need not be minimal.
The set is the first argument, as the predicate is the first argument of `Minimal`, so that
`Exemplifies p` is the predicate of exemplifying `p`.

## References

* [kratzer-2012]
* [deigan-2020]
* [bondarenko-2022]
-/

@[expose] public section

open Set Topology

namespace Mereology

variable {α : Type*} [TopologicalSpace α]

section TopologicalSpace

variable {p q u : Set α} {x : α}

/-- `x` exemplifies `p` when it is an interior point or an isolated point of `p`. -/
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

/-- Whether `x` exemplifies a set depends only on the germ of the set at `x`. -/
theorem exemplifies_congr (h : p =ᶠ[𝓝 x] q) : Exemplifies p x ↔ Exemplifies q x := by
  have h' := Filter.eventuallyEqSet_iff.1 h
  simp only [Exemplifies, mem_interior_iff_mem_nhds, mem_sdiff, mem_derivedSet,
    accPt_iff_frequently]
  exact or_congr (Filter.eventually_congr h') (and_congr h'.self_of_nhds
    (not_congr (Filter.frequently_congr (h'.mono fun _ hy ↦ and_congr_right fun _ ↦ hy))))

/-- Whether `x` exemplifies a set depends only on the set in a neighbourhood of `x`. -/
theorem dependsOn_exemplifies (hu : u ∈ 𝓝 x) : Set.DependsOn (Exemplifies · x) u :=
  fun _ ↦ propext <| exemplifies_congr <| Filter.eventuallyEqSet_iff.2 <| by
    filter_upwards [hu] with y hy
    simp [hy]

/-- A set has no exemplifier exactly when it has empty interior and no isolated point. -/
theorem forall_not_exemplifies_iff :
    (∀ x, ¬ Exemplifies p x) ↔ interior p = ∅ ∧ Preperfect p := by
  simp only [Exemplifies, not_or, forall_and, eq_empty_iff_forall_notMem, mem_sdiff, not_and,
    not_not, preperfect_iff_subset_derivedSet, subset_def]

end TopologicalSpace

section PartialOrder

variable [PartialOrder α] [Topology.IsLowerSet α] {p q s : Set α} {x y z : α}

open Topology.IsLowerSet

/-- In a part order, `x` exemplifies `p` when every part of `x` is in `p` or `x` is a minimal
member of `p`. -/
theorem exemplifies_iff : Exemplifies p x ↔ Iic x ⊆ p ∨ Minimal (· ∈ p) x := by
  simp only [Exemplifies, mem_interior_iff_mem_nhds, mem_sdiff, mem_derivedSet,
    accPt_iff_frequently, nhds_eq_principal_Iic, Filter.mem_principal,
    Filter.frequently_principal, minimal_iff_forall_lt]
  exact or_congr_right (and_congr_right fun _ ↦
    ⟨fun h y hy hyp ↦ h ⟨y, hy.le, hy.ne, hyp⟩,
      fun h ⟨y, hyx, hne, hyp⟩ ↦ h (lt_of_le_of_ne hyx hne) hyp⟩)

/-- Whether `x` exemplifies a set depends only on its members among the parts of `x`. -/
theorem dependsOn_exemplifies_Iic (x : α) : Set.DependsOn (Exemplifies · x) (Iic x) :=
  dependsOn_exemplifies (by rw [nhds_eq_principal_Iic]; exact Filter.mem_principal_self _)

instance [Fintype α] [DecidableLE α] [DecidablePred (· ∈ p)] : DecidablePred (Exemplifies p) :=
  fun x ↦ decidable_of_iff ((∀ y ≤ x, y ∈ p) ∨ x ∈ p ∧ ∀ y ∈ p, y ≤ x → x ≤ y)
    exemplifies_iff.symm

theorem _root_.Minimal.exemplifies (h : Minimal (· ∈ p) x) : Exemplifies p x :=
  exemplifies_iff.2 (.inr h)

theorem exemplifies_iff_imp_minimal :
    Exemplifies p x ↔ ((∃ y ≤ x, y ∉ p) → Minimal (· ∈ p) x) := by
  simp [exemplifies_iff, subset_def, or_iff_not_imp_left]

theorem exemplifies_iff_mem_and :
    Exemplifies p x ↔ x ∈ p ∧ ((∀ y < x, y ∈ p) ∨ ∀ y < x, y ∉ p) := by
  rw [exemplifies_iff, minimal_iff_forall_lt, and_or_left]
  refine or_congr ⟨fun h ↦ ⟨h self_mem_Iic, fun y hy ↦ h hy.le⟩, fun h y hy ↦ ?_⟩ .rfl
  obtain rfl | hlt := (mem_Iic.1 hy).eq_or_lt
  exacts [h.1, h.2 y hlt]

/-- Something with a proper part in `p` exemplifies `p` only if all of its parts are in `p`. -/
theorem Exemplifies.Iic_subset (h : Exemplifies p x) (hy : y < x) (hyp : y ∈ p) : Iic x ⊆ p :=
  (exemplifies_iff.1 h).resolve_right fun hmin ↦ hmin.not_prop_of_lt hy hyp

/-- Something with a part outside `p` exemplifies `p` only if it is a minimal member of `p`. -/
theorem Exemplifies.minimal (h : Exemplifies p x) (hy : y ≤ x) (hyp : y ∉ p) :
    Minimal (· ∈ p) x :=
  (exemplifies_iff.1 h).resolve_left fun hsub ↦ hyp (hsub hy)

theorem not_exemplifies_of_lt (hy : y < x) (hyp : y ∈ p) (hz : z ≤ x) (hzp : z ∉ p) :
    ¬ Exemplifies p x :=
  fun h ↦ hzp (h.Iic_subset hy hyp hz)

theorem _root_.IsLowerSet.exemplifies_iff (hp : IsLowerSet p) : Exemplifies p x ↔ x ∈ p :=
  (isOpen_iff_isLowerSet.2 hp).exemplifies_iff

theorem _root_.IsAntichain.exemplifies_iff (hp : IsAntichain (· ≤ ·) p) :
    Exemplifies p x ↔ x ∈ p :=
  ⟨Exemplifies.mem, fun hx ↦ Minimal.exemplifies ⟨hx, fun y hy hyx ↦ by
    obtain rfl | hne := eq_or_ne y x
    exacts [le_rfl, absurd hyx (hp hy hx hne)]⟩⟩

/-- The exemplifiers of the closure of `s` are its interior points and the minimal elements of
`s`. -/
theorem exemplifies_upperClosure_iff :
    Exemplifies (upperClosure s : Set α) x ↔
      Iic x ⊆ upperClosure s ∨ Minimal (· ∈ s) x := by
  rw [exemplifies_iff]
  exact or_congr_right minimal_mem_upperClosure_iff

/-- The exemplifiers of the upper closure of an antichain none of whose members is minimal are
the members of the antichain. -/
theorem _root_.IsAntichain.exemplifies_upperClosure_iff (hs : IsAntichain (· ≤ ·) s)
    (hmin : ∀ a ∈ s, ¬ IsMin a) : Exemplifies (upperClosure s : Set α) x ↔ x ∈ s := by
  rw [Mereology.exemplifies_upperClosure_iff]
  refine ⟨fun h ↦ h.elim (fun hsub ↦ ?_) fun h ↦ h.prop, fun h ↦ .inr ⟨h, fun y hy hyx ↦ ?_⟩⟩
  · obtain ⟨a, ha, hax⟩ := hsub self_mem_Iic
    obtain ⟨b, hba⟩ := not_isMin_iff.1 (hmin a ha)
    obtain ⟨c, hc, hcb⟩ := hsub (hba.le.trans hax)
    exact absurd (hcb.trans hba.le) (hs hc ha (hcb.trans_lt hba).ne)
  · obtain rfl | hne := eq_or_ne y x
    exacts [le_rfl, absurd hyx (hs hy h hne)]

/-- In a well-founded part order a closed set is the closure of its exemplifiers. -/
theorem closure_setOf_exemplifies [WellFoundedLT α] (hp : IsClosed p) :
    closure {x | Exemplifies p x} = p := by
  have hsub : {x | Exemplifies p x} ⊆ p := fun _ h ↦ Exemplifies.mem h
  refine (closure_minimal hsub hp).antisymm fun x hx ↦ ?_
  obtain ⟨m, hmx, hm⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ p) x hx
  rw [closure_eq_upperClosure]
  exact ⟨m, hm.exemplifies, hmx⟩

/-- The minimal members of a closed set are the generic points of its irreducible components:
the closure of `x` is a maximal irreducible subset of `p` exactly when `x` is a minimal member of
`p`. -/
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

/-- The sum of a member of `p` and something outside `p` that is not part of it does not
exemplify `p`. -/
theorem not_exemplifies_sup [SemilatticeSup α] [Topology.IsLowerSet α] {p : Set α} {y z : α}
    (hy : y ∈ p) (hz : z ∉ p) (hzy : ¬ z ≤ y) : ¬ Exemplifies p (y ⊔ z) :=
  not_exemplifies_of_lt (left_lt_sup.2 hzy) hy le_sup_right hz

end Mereology
