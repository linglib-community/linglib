module

public import Linglib.Semantics.Questions.Partition.Basic

/-!
# Information and the answers to a partition question

Let `Q` be a partition question and let `J` be a set of worlds, the information that someone has.

A cell of `Q` is compatible with `J` when some world of `J` lies in it, so that `J` does not rule
that answer out. We write `Q.compatible J` for the set of compatible cells.

Information `J` is closer to an answer than weaker information `K` when `J` rules out a cell that
`K` leaves open. This is `Q.CloserToAnswer J K`, and it is how [groenendijk-stokhof-1984] define a
partial answer.

We also define the saturation `Q.saturation s` of a set of worlds, the union of the cells that it
meets.

## References

* [groenendijk-stokhof-1984]
-/

@[expose] public section

namespace Setoid

variable {W : Type*} {Q : Setoid W} {p q : Set W} {w v : W}

/-! ### Saturation -/

/-- The saturation of a set of worlds is the union of the cells it meets. -/
def saturation (Q : Setoid W) (s : Set W) : Set W := {v | ∃ w ∈ s, Q w v}

theorem subset_saturation (Q : Setoid W) (s : Set W) : s ⊆ Q.saturation s :=
  fun w hw ↦ ⟨w, hw, Q.refl' w⟩

@[simp] theorem saturation_bot (s : Set W) : (⊥ : Setoid W).saturation s = s := by
  ext w
  simp [saturation]

theorem determines_saturation (Q : Setoid W) (s : Set W) : Q.Determines (Q.saturation s) :=
  determines_iff.2 fun _ _ h ↦ ⟨fun ⟨w, hw, hwu⟩ ↦ ⟨w, hw, Q.trans' hwu h⟩,
    fun ⟨w, hw, hwv⟩ ↦ ⟨w, hw, Q.trans' hwv (Q.symm' h)⟩⟩

/-! ### Answers compatible with information -/

variable {J K : Set W}

/-- The cells of `Q` compatible with the information `J`, those that `J` does not rule out
([groenendijk-stokhof-1984]). -/
def compatible (Q : Setoid W) (J : Set W) : Set (Set W) := {X ∈ Q.classes | (X ∩ J).Nonempty}

theorem compatible_mono (Q : Setoid W) (h : J ⊆ K) : Q.compatible J ⊆ Q.compatible K :=
  fun _ hX ↦ ⟨hX.1, hX.2.mono (Set.inter_subset_inter_right _ h)⟩

/-- `J` is closer to an answer to `Q` than `K` when it lies within `K` and rules out a cell that
`K` leaves open. Information `K` updated with a proposition `p` receives a partial answer when
`K ∩ p` is closer to an answer than `K` ([groenendijk-stokhof-1984]). -/
def CloserToAnswer (Q : Setoid W) (J K : Set W) : Prop := J ⊆ K ∧ Q.compatible J ⊂ Q.compatible K

/-- `J` gives access to the true answer at `w` when the cell of `w` is compatible with it. -/
def GivesAccess (Q : Setoid W) (J : Set W) (w : W) : Prop := Q.cell w ∈ Q.compatible J

theorem givesAccess_iff : Q.GivesAccess J w ↔ (Q.cell w ∩ J).Nonempty :=
  and_iff_right (Q.mem_classes w)

theorem closerToAnswer_iff :
    Q.CloserToAnswer J K ↔ J ⊆ K ∧ ∃ w, (Q.cell w ∩ K).Nonempty ∧ ¬ (Q.cell w ∩ J).Nonempty := by
  refine and_congr_right fun hJK ↦ ?_
  rw [Set.ssubset_iff_of_subset (Q.compatible_mono hJK)]
  exact ⟨fun ⟨_, ⟨⟨w, rfl⟩, hK⟩, hJ⟩ ↦ ⟨w, hK, fun h ↦ hJ ⟨Q.mem_classes w, h⟩⟩,
    fun ⟨w, hK, hJ⟩ ↦ ⟨_, ⟨Q.mem_classes w, hK⟩, fun h ↦ hJ h.2⟩⟩

end Setoid
