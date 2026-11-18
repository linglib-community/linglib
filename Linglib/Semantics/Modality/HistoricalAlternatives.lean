module

public import Mathlib.Data.Set.Prod
public import Mathlib.Order.Interval.Set.Disjoint
public import Mathlib.Order.Interval.Set.LinearOrder
public import Linglib.Semantics.Index
public import Linglib.Semantics.Tense.Defs
public import Linglib.Logic.Temporal.Basic

/-!
# Historical alternatives

The historical alternatives of a world at a time are the worlds that match it in matters of
particular fact up to that time ([lewis-1979-time-arrow]): its class under the historical
equivalence of a T × W frame ([thomason-1984]). They are the metaphysical modal base of
[condoravdi-2002] and the modal parameter of *will* in [cariani-santorio-2018]. Since historical
equivalence gets finer as time advances, the alternatives of a world
[shrink over time](##Temporal.TWFrame.alternatives_anti). Paired with the times a tense cell
admits they give the oriented modal bases of [klecha-2016], whose doxastic base carries
[the Upper Limit Constraint](##Temporal.TWFrame.time_le_of_mem_actualHistoryBase) of
[abusch-1997]. A property is settled over a common ground when the alternatives of each of its
worlds agree on it, that is, when the property or its negation is
[historically necessary](##Temporal.TWFrame.isSettled_iff) there, and what is settled
[stays settled](##Temporal.TWFrame.IsSettled.mono).

## References

* [lewis-1979-time-arrow]
* [thomason-1984]
* [von-kutschera-1997]
* [condoravdi-2002]
* [cariani-santorio-2018]
* [klecha-2016]
* [abusch-1997]
-/

@[expose] public section

open Set
open scoped Denotes SetRel ModalLogic

namespace Temporal.TWFrame

variable {W T : Type*}

/-! ### The alternatives of a world at a time -/

section Alternatives

variable [Preorder T] (F : TWFrame W T) {w v : W} {t t' : T}

/-- The historical alternatives of a world–time index are the worlds historically equivalent to
its world at its time, the metaphysical modal base `MB(w, t)` of [condoravdi-2002]. -/
def alternatives (i : Index W T) : Set W := {v | F.sim i.time i.world v}

variable {F}

@[simp] theorem mem_alternatives : v ∈ F.alternatives ⟨w, t⟩ ↔ F.sim t w v := Iff.rfl

theorem mem_alternatives_self : w ∈ F.alternatives ⟨w, t⟩ := (F.sim t).refl' w

/-- Historical equivalence partitions the worlds, so an alternative of a world has the same
alternatives as the world. -/
theorem alternatives_eq_of_mem (h : v ∈ F.alternatives ⟨w, t⟩) :
    F.alternatives ⟨v, t⟩ = F.alternatives ⟨w, t⟩ :=
  Set.ext fun _ ↦ ⟨(F.sim t).trans' h, (F.sim t).trans' ((F.sim t).symm' h)⟩

/-- The alternatives of a world shrink as time advances. -/
theorem alternatives_anti (h : t ≤ t') : F.alternatives ⟨w, t'⟩ ⊆ F.alternatives ⟨w, t⟩ :=
  fun _ hv ↦ F.antitone_sim h hv

end Alternatives

/-! ### Bases oriented by a tense cell

A modal over historical alternatives evaluates its prejacent at the alternatives of its index
and at times oriented to the index's time by a tense cell, Condoravdi's temporal orientation
of a modal relative to its perspective. The historical base is oriented to the nonpast, and
Klecha's doxastic and circumstantial bases to the nonfuture and the future. -/

section Oriented

variable {C : PointAlgebra}

section Preorder

variable [Preorder T] (F : TWFrame W T) (s : Index W T) {s' : Index W T}

/-- The base of the alternatives oriented by a tense cell `C` pairs the alternatives of an index
with the times standing to the index's time in a position of `C`. -/
def orientedBase (C : PointAlgebra) : Set (Index W T) :=
  {s' | s'.world ∈ F.alternatives s ∧ s.time ~[PointAlgebra.toSetRel C] s'.time}

/-- The historical modal base, the alternatives at times at or after the index's own, the past
fixed and the future branching ([thomason-1984], [condoravdi-2002]). -/
abbrev historicalBase : Set (Index W T) := F.orientedBase s Tense.nonpast

/-- The actual-history base, [klecha-2016]'s doxastic base, the alternatives at times at or
before the index's own. -/
abbrev actualHistoryBase : Set (Index W T) := F.orientedBase s Tense.nonfuture

/-- The future-history base, [klecha-2016]'s circumstantial base, the alternatives at times
strictly after the index's own. -/
abbrev futureHistoryBase : Set (Index W T) := F.orientedBase s ⟦Tense.future⟧

variable {F s}

theorem mem_orientedBase :
    s' ∈ F.orientedBase s C ↔
      s'.world ∈ F.alternatives s ∧ s.time ~[PointAlgebra.toSetRel C] s'.time :=
  Iff.rfl

theorem mem_futureHistoryBase :
    s' ∈ F.futureHistoryBase s ↔ s'.world ∈ F.alternatives s ∧ s.time < s'.time := by
  rw [mem_orientedBase, Tense.mem_toSetRel_future]

theorem time_lt_of_mem_futureHistoryBase (h : s' ∈ F.futureHistoryBase s) : s.time < s'.time :=
  (mem_futureHistoryBase.1 h).2

theorem orientedBase_sup (C D : PointAlgebra) :
    F.orientedBase s (C ⊔ D) = F.orientedBase s C ∪ F.orientedBase s D := by
  ext
  simp only [mem_orientedBase, PointAlgebra.toSetRel_sup, Set.mem_union, and_or_left]

end Preorder

section PartialOrder

variable [PartialOrder T] {F : TWFrame W T} {s s' : Index W T}

theorem mem_historicalBase :
    s' ∈ F.historicalBase s ↔ s'.world ∈ F.alternatives s ∧ s.time ≤ s'.time := by
  rw [mem_orientedBase, Tense.nonpast_eq_present_sup_future, PointAlgebra.toSetRel_sup,
    Set.mem_union, Tense.mem_toSetRel_present, Tense.mem_toSetRel_future, le_iff_eq_or_lt, eq_comm]

theorem mem_actualHistoryBase :
    s' ∈ F.actualHistoryBase s ↔ s'.world ∈ F.alternatives s ∧ s'.time ≤ s.time := by
  rw [mem_orientedBase, Tense.nonfuture_eq_past_sup_present, PointAlgebra.toSetRel_sup,
    Set.mem_union, Tense.mem_toSetRel_past, Tense.mem_toSetRel_present, le_iff_lt_or_eq]

/-- A situation in the actual-history base is no later than the index, the Upper Limit
Constraint of [abusch-1997] as [klecha-2016] derives it from the doxastic base. -/
theorem time_le_of_mem_actualHistoryBase (h : s' ∈ F.actualHistoryBase s) : s'.time ≤ s.time :=
  (mem_actualHistoryBase.1 h).2

end PartialOrder

section LinearOrder

variable [LinearOrder T] {F : TWFrame W T} {s s' : Index W T}

/-- On linear time the time of a situation in an oriented base stands to the index's time in a
position of the cell. -/
theorem compare_mem_of_mem_orientedBase (h : s' ∈ F.orientedBase s C) :
    compare s'.time s.time ∈ C :=
  PointAlgebra.mem_toSetRel_iff.1 h.2

/-- On linear time the actual and future bases together hold the alternatives at all times. -/
theorem actualHistoryBase_union_futureHistoryBase :
    F.actualHistoryBase s ∪ F.futureHistoryBase s = Index.world ⁻¹' F.alternatives s := by
  rw [← orientedBase_sup, Tense.nonfuture_eq_compl_future, compl_sup_eq_top]
  ext
  simp [mem_orientedBase]

end LinearOrder

end Oriented

/-! ### Settledness -/

section Settled

variable [Preorder T] (F : TWFrame W T) {cg : Set W} {t t' : T} {P : W → Prop}

/-- A property is settled at a time over a common ground when the historical alternatives of
each of its worlds agree on it ([condoravdi-2002]). Past and present issues are settled, and
future ones need not be. -/
def IsSettled (cg : Set W) (t : T) (P : W → Prop) : Prop :=
  ∀ w ∈ cg, ∀ v ∈ F.alternatives ⟨w, t⟩, (P w ↔ P v)

variable {F}

/-- A property is settled at a time over a common ground exactly when, at every common-ground
world, it or its negation is historically necessary. -/
theorem isSettled_iff :
    F.IsSettled cg t P ↔ ∀ w ∈ cg, □[F.alt t] P w ∨ □[F.alt t] (fun v ↦ ¬ P v) w := by
  refine forall₂_congr fun w _ ↦ ⟨fun h ↦ ?_, fun h v hv ↦ ?_⟩
  · by_cases hw : P w
    exacts [.inl fun v hv ↦ (h v hv).1 hw, .inr fun v hv hv' ↦ hw ((h v hv).2 hv')]
  · rcases h with h | h
    · exact iff_of_true (h w ((F.sim t).refl' w)) (h v hv)
    · exact iff_of_false (h w ((F.sim t).refl' w)) (h v hv)

/-- What is settled at a time is settled at every later time. -/
theorem IsSettled.mono (h : F.IsSettled cg t P) (htt' : t ≤ t') : F.IsSettled cg t' P :=
  fun w hw v hv ↦ h w hw v (alternatives_anti htt' hv)

end Settled

end Temporal.TWFrame
