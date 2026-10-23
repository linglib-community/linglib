module

public import Mathlib.Basic.Rel
public import Mathlib.Data.Set.Lattice.Bounded

/-!
# Commitment states

A public commitment is a participant's undertaking to act as if a proposition holds, in the
tradition of Hamblin and Brandom. A commitment state relates holders to the propositions they are
committed to. The holders are whatever a framework distinguishes commitments by, such as the
participants, as for Gunlogson and for Farkas and Bruce, or a participant together with the
attitude the commitment is to, belief or preference, as for Condoravdi and Lauer. A holder's
commitment set is the set of worlds its commitments leave open, and adding a commitment narrows it
by the content. A commitment as a proposition, which a common ground can contain without
containing its content, is `Commitment.committed`.

## Main definitions

* `Commitment.State κ W`: a commitment state, a relation from holders to propositions.
* `Commitment.Force`: the attitude a commitment is to.
* `Commitment.State.contents`: the propositions a holder is committed to.
* `Commitment.State.commitmentSet`: the worlds a holder's commitments leave open, Gunlogson's
  commitment set.
* `Commitment.State.jointContents`: the propositions every holder is committed to.

## Main results

* `Commitment.State.commitmentSet_insert_self`, `Commitment.State.commitmentSet_insert_of_ne`:
  adding a commitment narrows its holder's commitment set by its content and leaves the other
  holders' alone.
* `Commitment.State.commitmentSet_subset_of_mem_jointContents`: what every holder is committed to
  holds throughout every commitment set.

## References

* [C. L. Hamblin, *Fallacies* (1970)][hamblin-1970]
* [R. Brandom, *Making It Explicit* (1994)][brandom-1994]
* [C. Gunlogson, *True to Form: Rising and Falling Declaratives as Questions in English*
  (2001)][gunlogson-2001]
* [D. F. Farkas and K. B. Bruce, *On Reacting to Assertions and Polar Questions*
  (2010)][farkas-bruce-2010]
* [C. Condoravdi and S. Lauer, *Imperatives: Meaning and illocutionary force*
  (2012)][condoravdi-lauer-2012]
-/

@[expose] public section

namespace Commitment

/-- The attitude a commitment is to, belief or preference. -/
inductive Force
  | doxastic
  | preferential
  deriving DecidableEq, Repr

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

/-- The joint contents of `K` are the propositions every holder is committed to. -/
def jointContents : Set (Set W) := ⋂ k, K.contents k

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

theorem mem_jointContents : p ∈ K.jointContents ↔ ∀ k, k ~[K] p := Set.mem_iInter

theorem commitmentSet_subset_of_mem_jointContents (h : p ∈ K.jointContents) (k : κ) :
    K.commitmentSet k ⊆ p :=
  commitmentSet_subset (mem_jointContents.1 h k)

end State

end Commitment
