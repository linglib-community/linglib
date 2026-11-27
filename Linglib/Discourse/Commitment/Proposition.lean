module

public import Linglib.Core.Relation.SetRel
public import Linglib.Logic.Modal.Systems
public import Linglib.Discourse.Commitment.Basic

/-!
# Commitment as a proposition

Let `O k` be an accessibility relation on worlds for each holder `k`, relating a world `w` to the
worlds compatible with what `k` is committed to at `w`. The proposition that `k` is committed to
`φ`, written `k ⊢[O] φ`, is the set of worlds all of whose `O k`-successors are in `φ`. Since it
is a proposition, a common ground can contain `k ⊢[O] φ` without containing `φ`.

The *performative update* by `k`'s commitment to `φ` removes from `O k` the pairs whose second
world is outside `φ`. After the update `k ⊢[O] φ` holds at every world.

When commitments do not vary from world to world they are given by a commitment set `P k` for
each holder, and `k ⊢[O] φ` then holds at every world or at none.

## Main definitions

* `k ⊢[O] φ`: the worlds all of whose `O k`-successors are in `φ`.
* `perform O k φ`: the relations `O`, with `O k` restricted to the pairs whose second world is in
  `φ`.
* `ofSets P`: the relations in which every world is related by `k` to exactly the worlds in
  `P k`.

## Main results

* `committed_perform`: `k ⊢[perform O k φ] ψ = k ⊢[O] (φᶜ ∪ ψ)`.
* `disjoint_committed_compl`: if `O k` is serial, then `k ⊢[O] φ` and `k ⊢[O] φᶜ` are disjoint.
* `committed_ofSets`: `k ⊢[ofSets P] φ` holds at every world if `P k ⊆ φ` and at none otherwise.
* `ofSets_commitmentSet_insert`: adding a commitment to a commitment state is the performative
  update of the relations given by its commitment sets.

## References

* [krifka-2015]
* [krifka-2024a]
* [van-der-leer-2026]
* [yamada-2012]
-/

@[expose] public section

namespace Commitment

open ModalLogic (IsSerial IsEuclidean IsK45Frame)
open scoped SetRel

variable {κ W : Type*} (O : κ → SetRel W W) (k : κ) (φ ψ : Set W)

/-- `k ⊢[O] φ` is the proposition that `k` is **committed** to `φ`: the set of worlds all of whose
`O k`-successors are in `φ`. -/
scoped notation:50 k:51 " ⊢[" O "] " φ:51 => SetRel.core (O k) φ

/-- The **performative update** of `O` by `k`'s commitment to `φ` restricts `O k` to the pairs whose
second world is in `φ` and leaves the other relations unchanged ([yamada-2012]'s update by an act of
asserting, [van-der-leer-2026] Definition 4). -/
def perform : κ → SetRel W W := fun k' ↦ {p | p ∈ O k' ∧ (k' = k → p.2 ∈ φ)}

variable {O k φ ψ} {k' : κ}

theorem disjoint_committed_compl [IsSerial (O k)] :
    Disjoint (k ⊢[O] φ) (k ⊢[O] φᶜ) :=
  Set.disjoint_left.2 fun w h h' ↦
    let ⟨_, hv⟩ := IsSerial.serial (R := O k) w
    h' hv (h hv)

@[simp] theorem mem_perform {p : W × W} :
    p ∈ perform O k φ k' ↔ p ∈ O k' ∧ (k' = k → p.2 ∈ φ) := .rfl

theorem perform_subset (k' : κ) : perform O k φ k' ⊆ O k' := fun _ h ↦ h.1

theorem perform_of_ne (h : k' ≠ k) : perform O k φ k' = O k' :=
  Set.ext fun _ ↦ ⟨And.left, fun hp ↦ ⟨hp, (absurd · h)⟩⟩

/-- After the performative update by `k`'s commitment to `φ`, `k` is committed to `ψ` at the worlds
where `k` was committed to `φᶜ ∪ ψ` ([yamada-2012]'s reduction axiom for the asserter's own
commitments). -/
theorem committed_perform : (k ⊢[perform O k φ] ψ) = (k ⊢[O] (φᶜ ∪ ψ)) :=
  Set.ext fun _ ↦ ⟨fun h _ hb ↦ or_iff_not_imp_left.2 fun ht ↦ h ⟨hb, fun _ ↦ not_not.1 ht⟩,
    fun h _ hb ↦ (h hb.1).resolve_left (not_not.2 (hb.2 rfl))⟩

theorem committed_perform_of_ne (h : k' ≠ k) :
    (k' ⊢[perform O k φ] ψ) = (k' ⊢[O] ψ) := by
  rw [perform_of_ne h]

@[simp] theorem committed_perform_self : (k ⊢[perform O k φ] φ) = Set.univ := by
  rw [committed_perform, Set.compl_union_self, SetRel.core_univ]

theorem perform_mono (h : φ ⊆ ψ) (k' : κ) : perform O k φ k' ⊆ perform O k ψ k' :=
  fun _ hp ↦ ⟨hp.1, fun e ↦ h (hp.2 e)⟩

theorem perform_perform : perform (perform O k φ) k ψ = perform O k (φ ∩ ψ) :=
  funext fun _ ↦ Set.ext fun _ ↦ by
    simp only [mem_perform, Set.mem_inter_iff]
    tauto

theorem perform_comm : perform (perform O k φ) k' ψ = perform (perform O k' ψ) k φ :=
  funext fun _ ↦ Set.ext fun _ ↦
    ⟨fun h ↦ ⟨⟨h.1.1, h.2⟩, h.1.2⟩, fun h ↦ ⟨⟨h.1.1, h.2⟩, h.1.2⟩⟩

/-- A family of relations is contained in the performative update of `O` by `k`'s commitment to `φ`
if and only if it is contained in `O` and, in it, `k` is committed to `φ` at every world. -/
theorem le_perform_iff {O' : κ → SetRel W W} :
    O' ≤ perform O k φ ↔ O' ≤ O ∧ (k ⊢[O'] φ) = Set.univ :=
  ⟨fun h ↦ ⟨fun k' ↦ (h k').trans (perform_subset k'),
      Set.eq_univ_of_forall fun _ _ hv ↦ (h k hv).2 rfl⟩,
    fun h k' p hp ↦ ⟨h.1 k' hp, fun e ↦ by
      subst e
      exact Set.eq_univ_iff_forall.1 h.2 p.1 hp⟩⟩

theorem perform_eq_self_iff : perform O k φ = O ↔ (k ⊢[O] φ) = Set.univ :=
  ⟨fun h ↦ (le_perform_iff.1 h.ge).2,
    fun h ↦ le_antisymm (fun k' ↦ perform_subset k') (le_perform_iff.2 ⟨le_rfl, h⟩)⟩

instance [IsK45Frame (O k')] : IsK45Frame (perform O k φ k') where
  trans _ _ _ h₁ h₂ := ⟨(O k').trans h₁.1 h₂.1, h₂.2⟩
  eucl _ _ _ h₁ h₂ := ⟨IsEuclidean.eucl _ _ _ h₁.1 h₂.1, h₂.2⟩

/-! ### Public commitment sets -/

variable (P : κ → Set W)

/-- `ofSets P` is the family of relations in which every world is related by `k` to exactly the
worlds in `P k`. -/
def ofSets : κ → SetRel W W := fun k ↦ SetRel.cgraph fun _ ↦ P k

instance : IsK45Frame (ofSets P k) where
  trans _ _ _ _ h := h
  eucl _ _ _ _ h := h

theorem committed_ofSets : (k ⊢[ofSets P] φ) = {_w | P k ⊆ φ} := rfl

theorem perform_ofSets : perform (ofSets P) k φ = ofSets fun k' ↦ {v ∈ P k' | k' = k → v ∈ φ} :=
  rfl

theorem ofSets_commitmentSet_insert (K : State κ W) (k : κ) (φ : Set W) :
    ofSets (insert (k, φ) K).commitmentSet = perform (ofSets K.commitmentSet) k φ := by
  rw [perform_ofSets]
  congr 1
  funext k'
  by_cases h : k' = k
  · subst h
    rw [State.commitmentSet_insert_self]
    ext
    simp [and_comm]
  · rw [State.commitmentSet_insert_of_ne h]
    ext
    simp [h]

end Commitment
