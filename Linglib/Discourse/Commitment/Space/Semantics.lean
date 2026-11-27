module

public import Linglib.Discourse.Commitment.Proposition
public import Linglib.Discourse.Commitment.Space.Basic

/-!
# Commitment Space Semantics

Commitment Space Semantics is the theory of commitment spaces whose states are sets of
propositions ordered by inclusion. A basic act adds propositions. An assertion by `k` of `φ` adds
the proposition `k ⊢[O] φ` that `k` is committed to `φ`, and a polar question proposes that the
addressee commit to `φ` or to `φᶜ`. The participant whose commitment an act projects is thus the
speaker of an assertion and the addressee of a question.

## Main definitions

* `Commitment.Space.assert`: the assertion.
* `Commitment.Space.monopolarQuestion`, `Commitment.Space.bipolarQuestion`: the polar questions.
* `Commitment.Space.ProjectsCommitment`: the act projects a participant's commitment on its
  content.

## Main results

* `Commitment.Space.projectsCommitment_Ici_assert_iff`,
  `Commitment.Space.projectsCommitment_Ici_bipolarQuestion_iff`: in the space of all states, an
  assertion projects only its author's commitment and a bipolar question only that of the
  participant it is put to, unless their commitments coincide.

## Implementation notes

After a question the root of an assertion carries the proposal as well, so an assertion on a
space need not add exactly its content to the common ground.

## References

* [cohen-krifka-2014]
* [krifka-2015]
* [van-der-leer-2026]
* [coppock-wechsler-2018]
-/

@[expose] public section

namespace Commitment

namespace Space

variable {κ W : Type*} (C : Space (Set (Set W))) (O : κ → SetRel W W) (k : κ) (φ : Set W)
  {d : Set (Set W)}

/-- The assertion `C + k⊢φ` adds the proposition that `k` is committed to `φ`
([cohen-krifka-2014] (37), [krifka-2015] (14)). -/
def assert : Space (Set (Set W)) := C.update {k ⊢[O] φ}

theorem mem_assert :
    d ∈ C.assert O k φ ↔ d = (C.assert O k φ).root ∨ d ∈ C ∧ (k ⊢[O] φ) ∈ d :=
  or_congr_right (and_congr_right fun _ ↦ Set.singleton_subset_iff)

theorem committed_mem_root_assert : (k ⊢[O] φ) ∈ (C.assert O k φ).root :=
  Set.singleton_subset_iff.1 (C.le_root_update _)

theorem root_assert_of_mem (h : insert (k ⊢[O] φ) C.root ∈ C) :
    (C.assert O k φ).root = insert (k ⊢[O] φ) C.root :=
  C.root_update_of_mem h

theorem root_mem_assert_iff : C.root ∈ C.assert O k φ ↔ (k ⊢[O] φ) ∈ C.root :=
  C.root_mem_update_iff.trans Set.singleton_subset_iff

theorem committed_mem_of_mem_assert (hd : d ∈ C.assert O k φ) : (k ⊢[O] φ) ∈ d :=
  ((C.mem_assert O k φ).1 hd).elim (· ▸ C.committed_mem_root_assert O k φ) And.right

/-- The monopolar question proposes `k`'s commitment to `φ` ([krifka-2015] (27)). -/
def monopolarQuestion : Space (Set (Set W)) := C.question {{k ⊢[O] φ}}

/-- The bipolar question proposes `k`'s commitment to `φ` or to `¬φ` ([krifka-2015] (23)). -/
def bipolarQuestion : Space (Set (Set W)) := C.question {{k ⊢[O] φ}, {k ⊢[O] φᶜ}}

theorem mem_monopolarQuestion :
    d ∈ C.monopolarQuestion O k φ ↔ d = C.root ∨ d ∈ C ∧ (k ⊢[O] φ) ∈ d := by
  simp [monopolarQuestion, mem_question]

theorem mem_bipolarQuestion :
    d ∈ C.bipolarQuestion O k φ ↔
      d = C.root ∨ d ∈ C ∧ ((k ⊢[O] φ) ∈ d ∨ (k ⊢[O] φᶜ) ∈ d) := by
  simp [bipolarQuestion, mem_question]

/-- The bipolar question is the disjunction of the monopolar questions of `φ` and of `¬φ`
([krifka-2015] (31)). -/
theorem coe_bipolarQuestion :
    (C.bipolarQuestion O k φ : Set (Set (Set W))) =
      ↑(C.monopolarQuestion O k φ) ∪ ↑(C.monopolarQuestion O k φᶜ) := by
  rw [bipolarQuestion, Set.insert_eq, coe_question_union]
  rfl

/-! ### Projected commitments -/

/-- An act taking `C` to `D` projects `k`'s commitment on `φ` when every state of `D` beyond the
root of `C` carries `k⊢φ` or `k⊢¬φ`. The participant whose commitment to its content an act
projects is its epistemic authority ([coppock-wechsler-2018]). -/
def ProjectsCommitment (D : Space (Set (Set W))) : Prop :=
  ∀ d ∈ D, d ≠ C.root → (k ⊢[O] φ) ∈ d ∨ (k ⊢[O] φᶜ) ∈ d

/-- An assertion projects its author's commitment. -/
theorem projectsCommitment_assert : C.ProjectsCommitment O k φ (C.assert O k φ) := fun _ hd _ ↦
  .inl (C.committed_mem_of_mem_assert O k φ hd)

/-- A bipolar question projects the commitment of the participant it is put to. -/
theorem projectsCommitment_bipolarQuestion :
    C.ProjectsCommitment O k φ (C.bipolarQuestion O k φ) := fun _ hd hne ↦
  (((C.mem_bipolarQuestion O k φ).1 hd).resolve_left hne).2

variable {O k φ} {l : κ}

/-- In the space of all states, an assertion by `l` projects `k`'s commitment only when `l`'s
commitment to `φ` is `k`'s commitment to `φ` or to `¬φ`. -/
theorem projectsCommitment_Ici_assert_iff :
    (Space.Ici ∅).ProjectsCommitment O k φ ((Space.Ici ∅).assert O l φ) ↔
      (k ⊢[O] φ) = (l ⊢[O] φ) ∨ (k ⊢[O] φᶜ) = (l ⊢[O] φ) := by
  refine ⟨fun h ↦ h {l ⊢[O] φ} (((Space.Ici ∅).mem_assert O l φ).2
    (.inr ⟨Set.empty_subset _, rfl⟩)) (Set.singleton_ne_empty _), fun h d hd _ ↦ ?_⟩
  have hl := (Space.Ici ∅).committed_mem_of_mem_assert O l φ hd
  rcases h with h | h <;> simp only [h, hl, true_or, or_true]

/-- In the space of all states, a bipolar question put to `l` projects `k`'s commitment only when
`l`'s commitments to `φ` and to `¬φ` are each `k`'s commitment to `φ` or to `¬φ`. -/
theorem projectsCommitment_Ici_bipolarQuestion_iff :
    (Space.Ici ∅).ProjectsCommitment O k φ ((Space.Ici ∅).bipolarQuestion O l φ) ↔
      ((k ⊢[O] φ) = (l ⊢[O] φ) ∨ (k ⊢[O] φᶜ) = (l ⊢[O] φ)) ∧
        ((k ⊢[O] φ) = (l ⊢[O] φᶜ) ∨ (k ⊢[O] φᶜ) = (l ⊢[O] φᶜ)) := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h d hd hne ↦ ?_⟩
  · exact h {l ⊢[O] φ} (((Space.Ici ∅).mem_bipolarQuestion O l φ).2
      (.inr ⟨Set.empty_subset _, .inl rfl⟩)) (Set.singleton_ne_empty _)
  · exact h {l ⊢[O] φᶜ} (((Space.Ici ∅).mem_bipolarQuestion O l φ).2
      (.inr ⟨Set.empty_subset _, .inr rfl⟩)) (Set.singleton_ne_empty _)
  · rcases (Space.Ici ∅).projectsCommitment_bipolarQuestion O l φ d hd hne with hl | hl
    · rcases h.1 with h | h <;> simp only [h, hl, true_or, or_true]
    · rcases h.2 with h | h <;> simp only [h, hl, true_or, or_true]

end Space

end Commitment
