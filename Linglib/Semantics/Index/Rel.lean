module

public import Linglib.Semantics.Index
public import Linglib.Logic.Modal.Defs

/-!
# Modal and temporal relations on indices

Modal and temporal accessibility are the same kind of object, a relation between world–time
indices ([kaufmann-condoravdi-harizanov-2006]). A modal relation links indices with one time,
and a temporal relation indices with one world: `Index.modal` lifts a relation between worlds
at each time, and `Index.temporal` a relation between times. Necessity along a lifted relation
is necessity along the original in the coordinate it moves
([`box_modal`](##Index.box_modal), [`box_temporal`](##Index.box_temporal)). The two lifts do not
commute in general. Stepping in time and then along a modal relation
[can be done in the other order](##Index.temporal_comp_modal_subset) when the worlds accessible
at the later time are accessible at the earlier one.

## References

* [kaufmann-condoravdi-harizanov-2006]
-/

@[expose] public section

open SetRel
open scoped ModalLogic

namespace Index

variable {W T : Type*} {R R' : T → SetRel W W} {S S' : SetRel T T} {i j : Index W T}
  {P : Index W T → Prop}

/-- The modal relation of a time-indexed family of relations between worlds links an index to
the indices at its time whose world its world accesses at that time. -/
def modal (R : T → SetRel W W) : SetRel (Index W T) (Index W T) :=
  {p | p.1.time = p.2.time ∧ p.1.world ~[R p.1.time] p.2.world}

/-- The temporal relation of a relation between times links an index to the indices in its
world at the times its time is related to. -/
def temporal (S : SetRel T T) : SetRel (Index W T) (Index W T) :=
  {p | p.1.world = p.2.world ∧ p.1.time ~[S] p.2.time}

@[simp] theorem mem_modal : i ~[modal R] j ↔ i.time = j.time ∧ i.world ~[R i.time] j.world :=
  Iff.rfl

@[simp] theorem mem_temporal : i ~[temporal S] j ↔ i.world = j.world ∧ i.time ~[S] j.time :=
  Iff.rfl

/-! ### Necessity and possibility -/

/-- Necessity along a modal relation is necessity along its relation between worlds, at the
time of the index. -/
theorem box_modal : □[modal R] P i ↔ □[R i.time] (fun v ↦ P ⟨v, i.time⟩) i.world := by
  refine ⟨fun h v hv ↦ h ⟨v, i.time⟩ ⟨rfl, hv⟩, ?_⟩
  rintro h ⟨v, u⟩ ⟨ht, hw⟩
  obtain rfl : i.time = u := ht
  exact h v hw

/-- Necessity along a temporal relation is necessity along its relation between times, in the
world of the index. -/
theorem box_temporal : □[temporal S] P i ↔ □[S] (fun u ↦ P ⟨i.world, u⟩) i.time := by
  refine ⟨fun h u hu ↦ h ⟨i.world, u⟩ ⟨rfl, hu⟩, ?_⟩
  rintro h ⟨v, u⟩ ⟨hw, ht⟩
  obtain rfl : i.world = v := hw
  exact h u ht

theorem diamond_modal : ◇[modal R] P i ↔ ◇[R i.time] (fun v ↦ P ⟨v, i.time⟩) i.world := by
  refine ⟨?_, fun ⟨v, hv, hP⟩ ↦ ⟨⟨v, i.time⟩, ⟨rfl, hv⟩, hP⟩⟩
  rintro ⟨⟨v, u⟩, ⟨ht, hw⟩, hP⟩
  obtain rfl : i.time = u := ht
  exact ⟨v, hw, hP⟩

theorem diamond_temporal : ◇[temporal S] P i ↔ ◇[S] (fun u ↦ P ⟨i.world, u⟩) i.time := by
  refine ⟨?_, fun ⟨u, hu, hP⟩ ↦ ⟨⟨i.world, u⟩, ⟨rfl, hu⟩, hP⟩⟩
  rintro ⟨⟨v, u⟩, ⟨hw, ht⟩, hP⟩
  obtain rfl : i.world = v := hw
  exact ⟨u, ht, hP⟩

/-! ### Algebra of the lifts -/

theorem modal_mono (h : ∀ t, R t ⊆ R' t) : modal R ⊆ modal R' :=
  fun _ hp ↦ ⟨hp.1, h _ hp.2⟩

theorem temporal_mono (h : S ⊆ S') : (temporal S : SetRel (Index W T) (Index W T)) ⊆ temporal S' :=
  fun _ hp ↦ ⟨hp.1, h hp.2⟩

theorem temporal_union (S S' : SetRel T T) :
    (temporal (S ∪ S') : SetRel (Index W T) (Index W T)) = temporal S ∪ temporal S' := by
  ext ⟨i, j⟩
  simp only [mem_temporal, Set.mem_union, and_or_left]

instance [∀ t, (R t).IsRefl] : (modal R).IsRefl := ⟨fun i ↦ ⟨rfl, (R i.time).rfl⟩⟩

instance [S.IsRefl] : (temporal S : SetRel (Index W T) (Index W T)).IsRefl :=
  ⟨fun _ ↦ ⟨rfl, S.rfl⟩⟩

instance [S.IsTrans] : (temporal S : SetRel (Index W T) (Index W T)).IsTrans :=
  ⟨fun _ _ _ h h' ↦ ⟨h.1.trans h'.1, S.trans h.2 h'.2⟩⟩

/-- A step along a modal relation and then along a temporal one moves the world at the first
index's time and then the time. -/
theorem mem_modal_comp_temporal :
    i ~[modal R ○ temporal S] j ↔ i.world ~[R i.time] j.world ∧ i.time ~[S] j.time := by
  refine ⟨?_, fun ⟨hw, hS⟩ ↦ ⟨⟨j.world, i.time⟩, ⟨rfl, hw⟩, rfl, hS⟩⟩
  rintro ⟨⟨v, u⟩, ⟨ht, hw⟩, hv, hS⟩
  obtain rfl : i.time = u := ht
  obtain rfl : v = j.world := hv
  exact ⟨hw, hS⟩

/-- A step in time followed by a modal step is a modal step followed by the step in time, when
the worlds accessible at the later time are accessible at the earlier one. -/
theorem temporal_comp_modal_subset (h : ∀ ⦃t u⦄, t ~[S] u → R u ⊆ R t) :
    temporal S ○ modal R ⊆ modal R ○ temporal S := by
  rintro ⟨i, j⟩ ⟨⟨v, u⟩, ⟨hv, hS⟩, ht, hw⟩
  obtain rfl : i.world = v := hv
  obtain rfl : u = j.time := ht
  exact mem_modal_comp_temporal.2 ⟨h hS hw, hS⟩

end Index
