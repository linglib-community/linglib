module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Minimal
public import Mathlib.Order.UpperLower.Closure

/-!
# Exemplification

In a situation semantics a proposition is a set of situations, and the situations are ordered by
parthood. A situation in which a proposition is true may contain much that has nothing to do
with its truth. A situation `x` *exemplifies* a set `p` when it contains nothing of that kind:
every part of `x` is in `p`, or `x` is a minimal member of `p`. A situation that is all mud
exemplifies the proposition that there is mud in the first way, and a situation with three
teapots and nothing else exemplifies the proposition that there are three teapots in the second.

Equivalently, `x` is a member of `p` whose proper parts are all members of `p` or all
non-members. Every member of a lower set exemplifies it, and every member of an antichain. Whether
`x` exemplifies `p` depends only on the members of `p` among the parts of `x`. If the members of
an antichain all have proper parts, the exemplifiers of its upper closure are its members, so
exemplification recovers a set of situations from the proposition that one of them is a part.

## Main definitions

* `Mereology.Exemplifies p x`: `x` exemplifies `p`.

## Main results

* `Mereology.exemplifies_iff_mem_and`: `x` exemplifies `p` iff `x` is a member of `p` whose
  proper parts are all members or all non-members.
* `Mereology.exemplifies_iff_imp_minimal`: `x` exemplifies `p` iff `x` is a minimal member of `p`
  whenever some part of `x` is not in `p`.
* `Mereology.not_exemplifies_of_lt`: something with a proper part in `p` and a part outside `p`
  does not exemplify `p`.
* `Mereology.Exemplifies.inter`: what exemplifies two sets exemplifies their intersection.
* `Mereology.exemplifies_congr`: exemplification by `x` depends only on the parts of `x`.
* `IsAntichain.exemplifies_upperClosure_iff`: the exemplifiers of the upper closure of an
  antichain without minimal elements are its members.

## Implementation notes

The definition is the disjunction of [kratzer-2012], whose two cases are the two ways of
exemplifying a proposition. The conjunctive form of [deigan-2020], which [bondarenko-2022] states
for arbitrary individuals and sets of them, is `Mereology.exemplifies_iff_mem_and`. The set is
the first argument, as the predicate is the first argument of `Minimal`, so that `Exemplifies p`
is the predicate of exemplifying `p`.

## References

* [kratzer-2012]
* [deigan-2020]
* [bondarenko-2022]
-/

@[expose] public section

namespace Mereology

variable {α : Type*}

section Preorder

variable [Preorder α] {p q : Set α} {x y z : α}

/-- `x` exemplifies `p` when every part of `x` is in `p` or `x` is a minimal member of `p`. -/
def Exemplifies (p : Set α) (x : α) : Prop :=
  Set.Iic x ⊆ p ∨ Minimal (· ∈ p) x

instance [Fintype α] [DecidableLE α] [DecidablePred (· ∈ p)] : DecidablePred (Exemplifies p) :=
  fun x ↦ decidable_of_iff ((∀ y ≤ x, y ∈ p) ∨ x ∈ p ∧ ∀ y ∈ p, y ≤ x → x ≤ y) .rfl

theorem Exemplifies.mem (h : Exemplifies p x) : x ∈ p :=
  h.elim (fun h ↦ h Set.self_mem_Iic) fun h ↦ h.prop

theorem _root_.Minimal.exemplifies (h : Minimal (· ∈ p) x) : Exemplifies p x := .inr h

theorem exemplifies_iff_imp_minimal :
    Exemplifies p x ↔ ((∃ y ≤ x, y ∉ p) → Minimal (· ∈ p) x) := by
  simp [Exemplifies, Set.subset_def, or_iff_not_imp_left]

/-- Something with a proper part in `p` exemplifies `p` only if all of its parts are in `p`. -/
theorem Exemplifies.Iic_subset (h : Exemplifies p x) (hy : y < x) (hyp : y ∈ p) : Set.Iic x ⊆ p :=
  h.resolve_right fun hmin ↦ hmin.not_prop_of_lt hy hyp

/-- Something with a part outside `p` exemplifies `p` only if it is a minimal member of `p`. -/
theorem Exemplifies.minimal (h : Exemplifies p x) (hy : y ≤ x) (hyp : y ∉ p) :
    Minimal (· ∈ p) x :=
  h.resolve_left fun hsub ↦ hyp (hsub hy)

theorem not_exemplifies_of_lt (hy : y < x) (hyp : y ∈ p) (hz : z ≤ x) (hzp : z ∉ p) :
    ¬ Exemplifies p x :=
  fun h ↦ hzp (h.Iic_subset hy hyp hz)

theorem _root_.IsLowerSet.exemplifies_iff (hp : IsLowerSet p) : Exemplifies p x ↔ x ∈ p :=
  ⟨Exemplifies.mem, fun hx ↦ .inl fun _ hy ↦ hp hy hx⟩

theorem _root_.IsAntichain.exemplifies_iff (hp : IsAntichain (· ≤ ·) p) :
    Exemplifies p x ↔ x ∈ p :=
  ⟨Exemplifies.mem, fun hx ↦ .inr ⟨hx, fun y hy hyx ↦ by
    obtain rfl | hne := eq_or_ne y x
    exacts [le_rfl, absurd hyx (hp hy hx hne)]⟩⟩

theorem Exemplifies.inter (hp : Exemplifies p x) (hq : Exemplifies q x) :
    Exemplifies (p ∩ q) x := by
  obtain hp | hp := hp
  · obtain hq | hq := hq
    · exact .inl (Set.subset_inter hp hq)
    · exact .inr (hq.and_left (hp Set.self_mem_Iic))
  · exact .inr (hp.and_right hq.mem)

/-- Whether `x` exemplifies a set depends only on its members among the parts of `x`. -/
theorem exemplifies_congr (h : p ∩ Set.Iic x = q ∩ Set.Iic x) :
    Exemplifies p x ↔ Exemplifies q x := by
  have hmem : ∀ y ≤ x, (y ∈ p ↔ y ∈ q) := fun y hy ↦ by
    simpa [Set.mem_Iic.2 hy] using Set.ext_iff.1 h y
  refine or_congr (forall_congr' fun y ↦ imp_congr_right fun hy ↦ hmem y hy)
    (and_congr (hmem x le_rfl) (forall_congr' fun y ↦ ?_))
  exact ⟨fun H hq hy ↦ H ((hmem y hy).2 hq) hy, fun H hp hy ↦ H ((hmem y hy).1 hp) hy⟩

end Preorder

section PartialOrder

variable [PartialOrder α] {p : Set α} {x y z : α}

theorem exemplifies_iff_mem_and :
    Exemplifies p x ↔ x ∈ p ∧ ((∀ y < x, y ∈ p) ∨ ∀ y < x, y ∉ p) := by
  rw [Exemplifies, minimal_iff_forall_lt, and_or_left]
  refine or_congr ⟨fun h ↦ ⟨h Set.self_mem_Iic, fun y hy ↦ h hy.le⟩, fun h y hy ↦ ?_⟩ .rfl
  obtain rfl | hlt := (Set.mem_Iic.1 hy).eq_or_lt
  exacts [h.1, h.2 y hlt]

/-- The exemplifiers of the upper closure of an antichain none of whose members is minimal are
the members of the antichain. -/
theorem _root_.IsAntichain.exemplifies_upperClosure_iff {s : Set α} (hs : IsAntichain (· ≤ ·) s)
    (hmin : ∀ a ∈ s, ¬ IsMin a) : Exemplifies (upperClosure s : Set α) x ↔ x ∈ s := by
  refine ⟨fun h ↦ ?_, fun h ↦ (hs.minimal_mem_upperClosure_iff_mem.2 h).exemplifies⟩
  obtain hsub | h := h
  · obtain ⟨a, ha, hax⟩ := hsub Set.self_mem_Iic
    obtain ⟨b, hba⟩ := not_isMin_iff.1 (hmin a ha)
    obtain ⟨c, hc, hcb⟩ := hsub (hba.le.trans hax)
    exact absurd (hcb.trans hba.le) (hs hc ha (hcb.trans_lt hba).ne)
  · exact hs.minimal_mem_upperClosure_iff_mem.1 h

end PartialOrder

/-- The sum of a member of `p` and something outside `p` that is not part of it does not
exemplify `p`. -/
theorem not_exemplifies_sup [SemilatticeSup α] {p : Set α} {y z : α} (hy : y ∈ p) (hz : z ∉ p)
    (hzy : ¬ z ≤ y) : ¬ Exemplifies p (y ⊔ z) :=
  not_exemplifies_of_lt (left_lt_sup.2 hzy) hy le_sup_right hz

end Mereology
