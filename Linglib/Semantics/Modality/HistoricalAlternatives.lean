module

public import Mathlib.Data.Set.Prod
public import Mathlib.Order.Interval.Set.Disjoint
public import Mathlib.Order.Interval.Set.LinearOrder
public import Linglib.Semantics.Index
public import Linglib.Semantics.Tense.Defs
public import Linglib.Logic.Temporal.Basic
public import Linglib.Semantics.Index.Rel

/-!
# Historical alternatives

The *historical alternatives* of a world at a time are the worlds historically equivalent to it
at that time in a T × W frame. This file defines them (`TWFrame.alternatives`), the modal bases
that pair them with the times of a tense cell (`TWFrame.orientedBase`), and settledness of a
property over a common ground (`TWFrame.IsSettled`). The alternatives of a world
[shrink as time advances](##Temporal.TWFrame.alternatives_anti). A property is settled when it
or its negation is [historically necessary](##Temporal.TWFrame.isSettled_iff) at each world of
the common ground; it then [stays settled](##Temporal.TWFrame.IsSettled.mono) and is
[historically possible only where it holds](##Temporal.TWFrame.IsSettled.diamond_iff).

## References

* [lewis-1979-time-arrow]
* [thomason-1984]
* [von-kutschera-1997]
* [condoravdi-2002]
* [kaufmann-condoravdi-harizanov-2006]
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

/-- `F.alternatives i` is the set of worlds historically equivalent to the world of `i` at the
time of `i`, the metaphysical modal base of [condoravdi-2002]. -/
def alternatives (i : Index W T) : Set W := {v | F.sim i.time i.world v}

variable {F}

@[simp] theorem mem_alternatives : v ∈ F.alternatives ⟨w, t⟩ ↔ F.sim t w v := Iff.rfl

theorem mem_alternatives_self : w ∈ F.alternatives ⟨w, t⟩ := (F.sim t).refl' w

omit F in
@[simp] theorem sim_ofDatedFacts {Fact : Type*} {time : Fact → T} {holds : W → Fact → Prop} :
    (ofDatedFacts time holds).sim t w v ↔ ∀ f, time f ≤ t → (holds w f ↔ holds v f) :=
  Iff.rfl

/-- A historical alternative of a world has the same historical alternatives. -/
theorem alternatives_eq_of_mem (h : v ∈ F.alternatives ⟨w, t⟩) :
    F.alternatives ⟨v, t⟩ = F.alternatives ⟨w, t⟩ :=
  Set.ext fun _ ↦ ⟨(F.sim t).trans' h, (F.sim t).trans' ((F.sim t).symm' h)⟩

/-- The historical alternatives of a world at a time are among its alternatives at every earlier
time ([thomason-1984]). -/
theorem alternatives_anti (h : t ≤ t') : F.alternatives ⟨w, t'⟩ ⊆ F.alternatives ⟨w, t⟩ :=
  fun _ hv ↦ F.antitone_sim h hv

end Alternatives

/-! ### Bases oriented by a tense cell

An oriented base relates an index to the historical alternatives of its world at the times a
tense cell admits: a step along historical equivalence followed by a step in time. -/

section Oriented

variable {C : PointAlgebra}

section Preorder

variable [Preorder T] (F : TWFrame W T) {s s' : Index W T}

/-- `F.orientedBase C` relates an index `⟨w, t⟩` to the indices `⟨v, u⟩` with `v` a historical
alternative of `w` at `t` and `u` standing to `t` in a position of the cell `C`. -/
def orientedBase (C : PointAlgebra) : SetRel (Index W T) (Index W T) :=
  F.historical ○ Index.temporal (PointAlgebra.toSetRel C)

/-- The oriented base of the nonpast: historical alternatives at the same or a later time
([condoravdi-2002]). -/
abbrev historicalBase : SetRel (Index W T) (Index W T) := F.orientedBase Tense.nonpast

/-- The oriented base of the nonfuture: historical alternatives at the same or an earlier time,
the doxastic base of [klecha-2016]. -/
abbrev actualHistoryBase : SetRel (Index W T) (Index W T) := F.orientedBase Tense.nonfuture

/-- The oriented base of the future: historical alternatives at a later time, the circumstantial
base of [klecha-2016]. -/
abbrev futureHistoryBase : SetRel (Index W T) (Index W T) := F.orientedBase ⟦Tense.future⟧

variable {F}

theorem mem_orientedBase :
    s ~[F.orientedBase C] s' ↔
      s'.world ∈ F.alternatives s ∧ s.time ~[PointAlgebra.toSetRel C] s'.time :=
  Index.mem_modal_comp_temporal

/-- Necessity along an oriented base is historical necessity of necessity at the times of the
cell. -/
theorem box_orientedBase (P : Index W T → Prop) :
    □[F.orientedBase C] P =
      □[F.historical] (□[Index.temporal (PointAlgebra.toSetRel C)] P) :=
  ModalLogic.box_comp _ _ P

theorem mem_futureHistoryBase :
    s ~[F.futureHistoryBase] s' ↔ s'.world ∈ F.alternatives s ∧ s.time < s'.time := by
  rw [mem_orientedBase, Tense.mem_toSetRel_future]

theorem time_lt_of_mem_futureHistoryBase (h : s ~[F.futureHistoryBase] s') : s.time < s'.time :=
  (mem_futureHistoryBase.1 h).2

theorem orientedBase_sup (C D : PointAlgebra) :
    F.orientedBase (C ⊔ D) = F.orientedBase C ∪ F.orientedBase D := by
  ext ⟨s, s'⟩
  simp only [mem_orientedBase, PointAlgebra.toSetRel_sup, Set.mem_union, and_or_left]

end Preorder

section PartialOrder

variable [PartialOrder T] {F : TWFrame W T} {s s' : Index W T}

theorem mem_historicalBase :
    s ~[F.historicalBase] s' ↔ s'.world ∈ F.alternatives s ∧ s.time ≤ s'.time := by
  rw [mem_orientedBase, Tense.nonpast_eq_present_sup_future, PointAlgebra.toSetRel_sup,
    Set.mem_union, Tense.mem_toSetRel_present, Tense.mem_toSetRel_future, le_iff_eq_or_lt, eq_comm]

theorem mem_actualHistoryBase :
    s ~[F.actualHistoryBase] s' ↔ s'.world ∈ F.alternatives s ∧ s'.time ≤ s.time := by
  rw [mem_orientedBase, Tense.nonfuture_eq_past_sup_present, PointAlgebra.toSetRel_sup,
    Set.mem_union, Tense.mem_toSetRel_past, Tense.mem_toSetRel_present, le_iff_lt_or_eq]

/-- An index accessible along the actual-history base is no later than the index it is accessible
from, the Upper Limit Constraint of [abusch-1997]. -/
theorem time_le_of_mem_actualHistoryBase (h : s ~[F.actualHistoryBase] s') : s'.time ≤ s.time :=
  (mem_actualHistoryBase.1 h).2

end PartialOrder

section LinearOrder

variable [LinearOrder T] {F : TWFrame W T} {s s' : Index W T}

/-- On a linear order, the time of an index accessible along an oriented base stands to the time
of the index it is accessible from in a position of the cell. -/
theorem compare_mem_of_mem_orientedBase (h : s ~[F.orientedBase C] s') :
    compare s'.time s.time ∈ C :=
  PointAlgebra.mem_toSetRel_iff.1 (mem_orientedBase.1 h).2

/-- On a linear order, the actual-history and future-history bases together relate an index to
the historical alternatives of its world at every time. -/
theorem mem_actualHistoryBase_union_futureHistoryBase :
    s ~[F.actualHistoryBase ∪ F.futureHistoryBase] s' ↔ s'.world ∈ F.alternatives s := by
  rw [← orientedBase_sup, Tense.nonfuture_eq_compl_future, compl_sup_eq_top, mem_orientedBase]
  simp

end LinearOrder

end Oriented

/-! ### Settledness -/

section Settled

variable [Preorder T] (F : TWFrame W T) {cg : Set W} {t t' : T} {P : W → Prop}

/-- A property `P` of worlds is *settled* at `t` over a common ground `cg` when every world of
`cg` agrees on `P` with each of its historical alternatives at `t` ([condoravdi-2002]). -/
def IsSettled (cg : Set W) (t : T) (P : W → Prop) : Prop :=
  ∀ w ∈ cg, ∀ v ∈ F.alternatives ⟨w, t⟩, (P w ↔ P v)

variable {F}

/-- A property is settled at `t` over `cg` if and only if at every world of `cg` it or its
negation is historically necessary at `t`. -/
theorem isSettled_iff :
    F.IsSettled cg t P ↔ ∀ w ∈ cg, □[F.alt t] P w ∨ □[F.alt t] (fun v ↦ ¬ P v) w := by
  refine forall₂_congr fun w _ ↦ ⟨fun h ↦ ?_, fun h v hv ↦ ?_⟩
  · by_cases hw : P w
    exacts [.inl fun v hv ↦ (h v hv).1 hw, .inr fun v hv hv' ↦ hw ((h v hv).2 hv')]
  · rcases h with h | h
    · exact iff_of_true (h w ((F.sim t).refl' w)) (h v hv)
    · exact iff_of_false (h w ((F.sim t).refl' w)) (h v hv)

/-- A property settled at a time is settled at every later time. -/
theorem IsSettled.mono (h : F.IsSettled cg t P) (htt' : t ≤ t') : F.IsSettled cg t' P :=
  fun w hw v hv ↦ h w hw v (alternatives_anti htt' hv)

/-- A property is settled over all worlds if and only if historically equivalent worlds agree
on it ([kaufmann-condoravdi-harizanov-2006]). -/
theorem isSettled_univ_iff :
    F.IsSettled univ t P ↔ ∀ ⦃w v⦄, F.sim t w v → (P w ↔ P v) :=
  ⟨fun h _ _ hv ↦ h _ trivial _ hv, fun h _ _ _ hv ↦ h hv⟩

/-- At a world of a common ground over which a property is settled, the property is historically
possible if and only if it holds. -/
theorem IsSettled.diamond_iff {w : W} (h : F.IsSettled cg t P) (hw : w ∈ cg) :
    ◇[F.alt t] P w ↔ P w :=
  ⟨fun ⟨v, hv, hP⟩ ↦ (h w hw v hv).2 hP, fun hP ↦ ⟨w, (F.sim t).refl' w, hP⟩⟩

/-- If membership in `cg` is settled over all worlds, then a property is settled over `cg` if and
only if its conjunction with membership in `cg` is settled over all worlds. -/
theorem isSettled_iff_isSettled_univ_and (hcg : F.IsSettled univ t (· ∈ cg)) :
    F.IsSettled cg t P ↔ F.IsSettled univ t (fun w ↦ w ∈ cg ∧ P w) := by
  refine ⟨fun h w _ v hv ↦ ?_, fun h w hw v hv ↦ ?_⟩
  · have hc := hcg w trivial v hv
    by_cases hw : w ∈ cg
    · exact and_congr hc (h w hw v hv)
    · exact iff_of_false (fun h' ↦ hw h'.1) fun h' ↦ hw (hc.2 h'.1)
  · have hP := h w trivial v hv
    exact ⟨fun hw' ↦ (hP.1 ⟨hw, hw'⟩).2, fun hv' ↦ (hP.2 ⟨(hcg w trivial v hv).1 hw, hv'⟩).2⟩

end Settled

end Temporal.TWFrame
