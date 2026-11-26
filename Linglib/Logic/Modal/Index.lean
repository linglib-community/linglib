module

public import Linglib.Logic.Modal.Index.Defs
public import Linglib.Logic.Modal.Defs

/-!
# Modal and temporal relations on indices

A relation between world–time indices is *modal* when it relates indices at one time and
*temporal* when it relates indices in one world ([kaufmann-condoravdi-harizanov-2006]). This file
defines the modal relation `Index.modal R` of a family `R` of relations between worlds indexed by
times, and the temporal relation `Index.temporal S` of a relation `S` between times. Necessity
along either is necessity along the underlying relation ([modal](##Index.box_modal),
[temporal](##Index.box_temporal)). A temporal step followed by a modal step
[is a modal step followed by a temporal step](##Index.temporal_comp_modal_subset) when the
worlds accessible at the later time are accessible at the earlier one.

## References

* [kaufmann-condoravdi-harizanov-2006]
-/

@[expose] public section

open SetRel
open scoped ModalLogic

namespace Index

variable {W T : Type*} {R R' : T → SetRel W W} {S S' : SetRel T T} {i j : Index W T}
  {P : Index W T → Prop}

/-- `Index.modal R` relates an index `⟨w, t⟩` to the indices `⟨v, t⟩` with `w ~[R t] v`. -/
def modal (R : T → SetRel W W) : SetRel (Index W T) (Index W T) :=
  {(i, j) | i.time = j.time ∧ i.world ~[R i.time] j.world}

/-- `Index.temporal S` relates an index `⟨w, t⟩` to the indices `⟨w, u⟩` with `t ~[S] u`. -/
def temporal (S : SetRel T T) : SetRel (Index W T) (Index W T) :=
  {(i, j) | i.world = j.world ∧ i.time ~[S] j.time}

@[simp] theorem mem_modal : i ~[modal R] j ↔ i.time = j.time ∧ i.world ~[R i.time] j.world :=
  Iff.rfl

@[simp] theorem mem_temporal : i ~[temporal S] j ↔ i.world = j.world ∧ i.time ~[S] j.time :=
  Iff.rfl

/-! ### Necessity and possibility -/

theorem box_modal : □[modal R] P i ↔ □[R i.time] (fun v ↦ P ⟨v, i.time⟩) i.world := by
  refine ⟨fun h v hv ↦ h ⟨v, i.time⟩ ⟨rfl, hv⟩, ?_⟩
  rintro h ⟨v, u⟩ ⟨ht, hw⟩
  obtain rfl : i.time = u := ht
  exact h v hw

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

theorem inv_temporal (S : SetRel T T) :
    (temporal S : SetRel (Index W T) (Index W T)).inv = temporal S.inv := by
  ext ⟨i, j⟩
  exact and_congr_left fun _ ↦ eq_comm

instance [∀ t, (R t).IsRefl] : (modal R).IsRefl := ⟨fun i ↦ ⟨rfl, (R i.time).rfl⟩⟩

instance [S.IsRefl] : (temporal S : SetRel (Index W T) (Index W T)).IsRefl :=
  ⟨fun _ ↦ ⟨rfl, S.rfl⟩⟩

instance [S.IsTrans] : (temporal S : SetRel (Index W T) (Index W T)).IsTrans :=
  ⟨fun _ _ _ h h' ↦ ⟨h.1.trans h'.1, S.trans h.2 h'.2⟩⟩

theorem mem_modal_comp_temporal :
    i ~[modal R ○ temporal S] j ↔ i.world ~[R i.time] j.world ∧ i.time ~[S] j.time := by
  refine ⟨?_, fun ⟨hw, hS⟩ ↦ ⟨⟨j.world, i.time⟩, ⟨rfl, hw⟩, rfl, hS⟩⟩
  rintro ⟨⟨v, u⟩, ⟨ht, hw⟩, hv, hS⟩
  obtain rfl : i.time = u := ht
  obtain rfl : v = j.world := hv
  exact ⟨hw, hS⟩

/-- If `R u ⊆ R t` whenever `t ~[S] u`, then a temporal step followed by a modal step is a modal
step followed by a temporal step. -/
theorem temporal_comp_modal_subset (h : ∀ ⦃t u⦄, t ~[S] u → R u ⊆ R t) :
    temporal S ○ modal R ⊆ modal R ○ temporal S := by
  rintro ⟨i, j⟩ ⟨⟨v, u⟩, ⟨hv, hS⟩, ht, hw⟩
  obtain rfl : i.world = v := hv
  obtain rfl : u = j.time := ht
  exact mem_modal_comp_temporal.2 ⟨h hS hw, hS⟩

end Index
