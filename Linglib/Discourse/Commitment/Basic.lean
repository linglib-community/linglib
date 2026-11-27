module

public import Mathlib.Basic.Rel
public import Mathlib.Data.Set.Lattice.Bounded

/-!
# Commitment states

A *commitment state* records what each holder is publicly committed to. It is a relation between
holders and propositions. A holder is whatever distinguishes one commitment from another: a
participant of the conversation, or a participant together with an attitude such as belief or
preference.

The *commitment set* of a holder is the set of worlds at which every proposition the holder is
committed to is true. Committing a holder to `φ` intersects the holder's commitment set with `φ`
and leaves the commitment sets of the other holders unchanged.

## Main definitions

* `State κ W`: a commitment state with holders `κ` and worlds `W`.
* `State.contents K k`: the propositions `k` is committed to in `K`.
* `State.commitmentSet K k`: the worlds that belong to every member of `K.contents k`.
* `State.Sincere K M w`: every holder `k` holds at `w`, under the attitude `M k`, each proposition
  in `K.contents k`.

## Main results

* `State.commitmentSet_insert_self`: committing `k` to `φ` intersects the commitment set of `k`
  with `φ`.
* `State.commitmentSet_insert_of_ne`: committing `k` to `φ` does not change the commitment set of
  another holder.

## References

* [hamblin-1970]
* [brandom-1994]
* [gunlogson-2001]
* [farkas-bruce-2010]
* [condoravdi-lauer-2012]
* [van-der-leer-2026]
-/

@[expose] public section

namespace Commitment

/-- A commitment state relates holders to the propositions they are committed to. -/
abbrev State (κ W : Type*) := SetRel κ (Set W)

namespace State

open scoped SetRel

variable {κ W : Type*} (K : State κ W) (k : κ)

/-- The contents of `k` in `K` are the propositions `k` is committed to. -/
def contents : Set (Set W) := {p | k ~[K] p}

/-- The commitment set of `k` in `K` is the set of worlds compatible with `k`'s commitments
([gunlogson-2001]'s `cs_k`). -/
def commitmentSet : Set W := ⋂₀ K.contents k

variable {K k} {L : State κ W} {k' : κ} {p φ : Set W}

@[simp] theorem mem_contents : p ∈ K.contents k ↔ k ~[K] p := .rfl

theorem mem_commitmentSet {w : W} : w ∈ K.commitmentSet k ↔ ∀ p, k ~[K] p → w ∈ p :=
  Set.mem_sInter

theorem commitmentSet_subset (h : k ~[K] p) : K.commitmentSet k ⊆ p :=
  Set.sInter_subset_of_mem h

theorem commitmentSet_anti (h : K ⊆ L) : L.commitmentSet k ⊆ K.commitmentSet k :=
  Set.sInter_subset_sInter fun _ hp ↦ h hp

@[simp] theorem contents_empty : (∅ : State κ W).contents k = ∅ := rfl

@[simp] theorem commitmentSet_empty : (∅ : State κ W).commitmentSet k = Set.univ :=
  Set.sInter_empty

@[simp] theorem contents_insert_self : (insert (k, φ) K).contents k = insert φ (K.contents k) := by
  ext
  simp [contents]

theorem contents_insert_of_ne (h : k' ≠ k) : (insert (k, φ) K).contents k' = K.contents k' := by
  ext
  simp [contents, h]

@[simp] theorem commitmentSet_insert_self :
    (insert (k, φ) K).commitmentSet k = φ ∩ K.commitmentSet k := by
  rw [commitmentSet, contents_insert_self, Set.sInter_insert]
  rfl

theorem commitmentSet_insert_of_ne (h : k' ≠ k) :
    (insert (k, φ) K).commitmentSet k' = K.commitmentSet k' := by
  rw [commitmentSet, contents_insert_of_ne h]
  rfl

/-! ### Sincerity -/

/-- A commitment state is sincere at `w` relative to the attitudes `M` when every holder holds at
`w`, under its attitude `M k`, each proposition it is committed to. -/
def Sincere (K : State κ W) (M : κ → W → Set (Set W)) (w : W) : Prop :=
  ∀ k p, k ~[K] p → p ∈ M k w


end State

end Commitment
