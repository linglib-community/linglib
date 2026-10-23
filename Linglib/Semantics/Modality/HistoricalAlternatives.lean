module

public import Mathlib.Data.Set.Prod
public import Mathlib.Order.Interval.Set.Disjoint
public import Mathlib.Order.Interval.Set.LinearOrder
public import Linglib.Semantics.Reference.Context.Index
public import Linglib.Semantics.Tense.Defs
public import Linglib.Logic.Temporal.Basic

/-!
# Historical alternatives

The historical alternatives of a world at a time are the worlds that perfectly match it in
matters of particular fact up to that time, Lewis's notion, which Cariani and Santorio take as
the modal base of *will*. A `HistoricalAlternatives` relation sends a world–time index to a set
of worlds; restricted to times from, up to, or strictly after the index's own, it gives
Condoravdi's historical base and Klecha's doxastic and circumstantial bases. A T × W frame
determines its alternatives, the classes of its historical equivalence.

## Main definitions

* `HistoricalAlternatives`, `metaphysicalBase`: the relation and its curried modal base.
* `orientedBase`: the alternatives at the times a tense cell admits, with `historicalBase`,
  `actualHistoryBase` and `futureHistoryBase` its nonpast, nonfuture and future instances.
* `Temporal.TWFrame.alternatives`: the historical alternatives of a T × W frame.
* `settled`, `diverse`: settledness over a common ground, and Condoravdi's diversity condition.

## Main results

* `time_le_of_mem_actualHistoryBase`: Abusch's Upper Limit Constraint for the doxastic base.
* `compare_mem_of_mem_orientedBase`: an oriented base admits only its cell's orientations.
* `actualHistoryBase_union_futureHistoryBase`: the actual and future bases together hold the
  alternatives at all times.
* `Temporal.TWFrame.alternatives_eq_of_mem`: the alternatives of an alternative are the same.
* `settled_not_diverse`: a settled property is not diverse.
* `settled_alternatives_iff`: over a frame, settledness is historical necessity of the property
  or its negation.

## References

* [D. Lewis, *Counterfactual dependence and time's arrow* (1979)][lewis-1979-time-arrow]
* [F. Cariani and P. Santorio, *Will done better: selection semantics, future credence, and
  indeterminacy* (2018)][cariani-santorio-2018]
* [C. Condoravdi, *Temporal interpretation of modals: modals for the present and for the
  past* (2002)][condoravdi-2002]
* [P. Klecha, *Modality and embedded temporal operators* (2016)][klecha-2016]
* [D. Abusch, *Sequence of tense and temporal de re* (1997)][abusch-1997]
* [R. H. Thomason, *Combinations of tense and modality* (1984)][thomason-1984]
* [F. von Kutschera, *T × W completeness* (1997)][von-kutschera-1997]
-/

@[expose] public section

open Set Semantics Kaplan
open scoped SetRel
open scoped ModalLogic

/-- The historical alternatives of a world–time index are the worlds that agree with its world
up to its time. -/
def HistoricalAlternatives (W T : Type*) := Index W T → Set W

namespace HistoricalAlternatives

variable {W T : Type*}

/-- The metaphysical modal base of [condoravdi-2002] is the relation curried, giving at a world
and time the worlds that share the world's history up to that time. -/
abbrev metaphysicalBase (history : HistoricalAlternatives W T) : W → T → Set W :=
  Function.curry history

/-! ### Bases oriented by a tense cell

A modal over historical alternatives evaluates its prejacent at the alternatives of its index
and at times oriented to the index's time by a tense cell, Condoravdi's temporal orientation
of a modal relative to its perspective. The historical base is oriented to the nonpast, and
Klecha's doxastic and circumstantial bases to the nonfuture and the future. -/

section Oriented

variable (history : HistoricalAlternatives W T) (s : Index W T) {s' : Index W T}
  {C : Finset Ordering}

/-- The base of the alternatives oriented by a tense cell `C` pairs the alternatives of an index
with the times standing to the index's time in a position of `C`. -/
def orientedBase [LT T] (C : Finset Ordering) : Set (Index W T) :=
  history s ×ˢ {t | s.time ~[Tense.toSetRel C] t}

/-- The historical modal base, the alternatives at times at or after the index's own, the past
fixed and the future branching ([thomason-1984], [condoravdi-2002]). -/
abbrev historicalBase [LT T] : Set (Index W T) := orientedBase history s Tense.nonpast

/-- The actual-history base, [klecha-2016]'s doxastic base, the alternatives at times at or
before the index's own. -/
abbrev actualHistoryBase [LT T] : Set (Index W T) := orientedBase history s ⟦Tense.future⟧ᶜ

/-- The future-history base, [klecha-2016]'s circumstantial base, the alternatives at times
strictly after the index's own. -/
abbrev futureHistoryBase [LT T] : Set (Index W T) := orientedBase history s ⟦Tense.future⟧

variable {history s}

theorem mem_orientedBase [LT T] :
    s' ∈ orientedBase history s C ↔ s'.world ∈ history s ∧ s.time ~[Tense.toSetRel C] s'.time :=
  Iff.rfl

theorem compare_mem_of_mem_orientedBase [LinearOrder T] (h : s' ∈ orientedBase history s C) :
    compare s'.time s.time ∈ C :=
  Tense.mem_toSetRel_iff_compare.1 h.2

theorem mem_historicalBase [PartialOrder T] :
    s' ∈ historicalBase history s ↔ s'.world ∈ history s ∧ s.time ≤ s'.time := by
  rw [mem_orientedBase, Tense.nonpast_eq_present_sup_future, Tense.toSetRel_sup, Set.mem_union,
    Tense.mem_toSetRel_present, Tense.mem_toSetRel_future, le_iff_eq_or_lt, eq_comm]

theorem mem_actualHistoryBase [PartialOrder T] :
    s' ∈ actualHistoryBase history s ↔ s'.world ∈ history s ∧ s'.time ≤ s.time := by
  rw [mem_orientedBase, ← Tense.past_sup_present, Tense.toSetRel_sup, Set.mem_union,
    Tense.mem_toSetRel_past, Tense.mem_toSetRel_present, le_iff_lt_or_eq]

theorem mem_futureHistoryBase [Preorder T] :
    s' ∈ futureHistoryBase history s ↔ s'.world ∈ history s ∧ s.time < s'.time := by
  rw [mem_orientedBase, Tense.mem_toSetRel_future]

theorem time_le_of_mem_actualHistoryBase [PartialOrder T] (h : s' ∈ actualHistoryBase history s) :
    s'.time ≤ s.time :=
  (mem_actualHistoryBase.1 h).2

theorem time_lt_of_mem_futureHistoryBase [Preorder T] (h : s' ∈ futureHistoryBase history s) :
    s.time < s'.time :=
  (mem_futureHistoryBase.1 h).2

theorem orientedBase_sup [LT T] (C D : Finset Ordering) :
    orientedBase history s (C ⊔ D) = orientedBase history s C ∪ orientedBase history s D := by
  ext
  simp only [mem_orientedBase, Tense.toSetRel_sup, Set.mem_union, and_or_left]

theorem actualHistoryBase_union_futureHistoryBase [LinearOrder T] :
    actualHistoryBase history s ∪ futureHistoryBase history s = history s ×ˢ Set.univ := by
  rw [← orientedBase_sup, compl_sup_eq_top]
  ext
  simp [mem_orientedBase]

end Oriented

/-! ### The alternatives of a T × W frame

The historical alternatives of a T × W frame are its classes of historical equivalence, so a
world is an alternative to itself and the alternatives of an alternative are the same. -/

end HistoricalAlternatives

namespace Temporal.TWFrame

open HistoricalAlternatives

variable {W T : Type*} [Preorder T] (F : TWFrame W T) {w v : W} {t : T}

/-- The historical alternatives of a frame, at an index the worlds historically equivalent to
its world at its time. -/
def alternatives : HistoricalAlternatives W T := fun i ↦ {v | F.sim i.time i.world v}

variable {F}

@[simp] theorem mem_alternatives : v ∈ F.alternatives (w, t) ↔ F.sim t w v := Iff.rfl

theorem mem_alternatives_self : w ∈ F.alternatives (w, t) := (F.sim t).iseqv.refl w

theorem alternatives_eq_of_mem (h : v ∈ F.alternatives (w, t)) :
    F.alternatives (v, t) = F.alternatives (w, t) :=
  Set.ext fun _ ↦ ⟨(F.sim t).iseqv.trans h, (F.sim t).iseqv.trans ((F.sim t).iseqv.symm h)⟩

end Temporal.TWFrame

namespace HistoricalAlternatives

variable {W T : Type*}

/-! ### Settledness and diversity -/

/-- A property is settled at a time over a common ground when the historical alternatives of
each of its worlds agree on it ([condoravdi-2002]). Past and present issues are settled, and
future ones need not be. -/
def settled (history : HistoricalAlternatives W T) (cg : Set W) (t : T) (P : W → Prop) : Prop :=
  ∀ w ∈ cg, ∀ w' ∈ history (w, t), (P w ↔ P w')

/-- A modal base meets the diversity condition of [condoravdi-2002] for a property when some
common-ground world sees worlds disagreeing on it. -/
def diverse (MB : W → T → Set W) (cg : Set W) (t : T) (P : W → Prop) : Prop :=
  ∃ w ∈ cg, ∃ w' ∈ MB w t, ∃ w'' ∈ MB w t, P w' ∧ ¬ P w''

theorem settled_not_diverse {history : HistoricalAlternatives W T} {MB : W → T → Set W}
    {cg : Set W} {t : T} {P : W → Prop} (hMB : ∀ w ∈ cg, MB w t ⊆ history (w, t))
    (h : settled history cg t P) : ¬ diverse MB cg t P :=
  fun ⟨w, hw, w', hw', w'', hw'', hP, hnP⟩ ↦
    hnP ((h w hw w'' (hMB w hw hw'')).mp ((h w hw w' (hMB w hw hw')).mpr hP))

theorem settled_alternatives_iff [Preorder T] {F : Temporal.TWFrame W T} {cg : Set W} {t : T}
    {P : W → Prop} :
    settled F.alternatives cg t P ↔ ∀ w ∈ cg, □[F.alt t] P w ∨ □[F.alt t] (fun v ↦ ¬ P v) w := by
  refine forall₂_congr fun w _ ↦ ⟨fun h ↦ ?_, fun h v hv ↦ ?_⟩
  · by_cases hw : P w
    exacts [.inl fun v hv ↦ (h v hv).1 hw, .inr fun v hv hv' ↦ hw ((h v hv).2 hv')]
  · rcases h with h | h
    · exact iff_of_true (h w ((F.sim t).iseqv.refl w)) (h v hv)
    · exact iff_of_false (h w ((F.sim t).iseqv.refl w)) (h v hv)

end HistoricalAlternatives
