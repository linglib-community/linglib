module

public import Linglib.Semantics.ArgumentStructure.AgentivityLattice.Persistence
public import Linglib.Semantics.Events.Lifespan

/-!
# Persistence from life spans

Grimm's persistence features say whether a participant exists, and keeps its qualities, at the
beginning and at the end of an event. Given the participant's life span, the event's run time and
the participant's qualities over time, Grimm's descriptions of the persistence levels assign the
participant [a level](##ArgumentStructure.Persistence.ofLifespan), whose features are the
persistence features the participant has: it [exists when the event
begins](##ArgumentStructure.Persistence.existsAtBeginning_mem_ofLifespan) and [keeps its qualities
to the end](##ArgumentStructure.Persistence.qualitiesAtEnd_mem_ofLifespan) exactly when the level
says so. A created participant, existing at the end of the event but not at the beginning, [does
not pre-exist the
event](##ArgumentStructure.Persistence.not_preExists_of_ofLifespan_eq_existentialEnd), and a
destroyed one [goes out of existence before the event
ends](##ArgumentStructure.Persistence.snd_lt_of_ofLifespan_eq_existentialBeginning).

## Implementation notes

A participant persists existentially at a boundary of the event when the boundary lies in its life
span. Its qualities are a function `q` of times, and it persists qualitatively at the end when it
exists there with the qualities it had at the beginning, if it existed then. Only the boundaries of
the event are compared, so a quality that changes and changes back counts as persisting. A
predicate's persistence level for an argument, the features it entails for every participant, is
not formalized.

## References

* [grimm-2011]
-/

@[expose] public section

namespace ArgumentStructure.Persistence

variable {T Q : Type*} [LinearOrder T] [DecidableEq Q] {life run : NonemptyInterval T} {q : T → Q}

/-- The persistence level of a participant with life span `life` and qualities `q` in an event with
run time `run`, by Grimm's descriptions: a participant existing at neither end does not persist,
one existing only at the beginning or only at the end persists existentially there, and one
existing at both ends persists totally or only at the beginning as its qualities are unchanged or
not ([grimm-2011] pp. 524–525). -/
def ofLifespan (life run : NonemptyInterval T) (q : T → Q) : Persistence :=
  if run.fst ∈ life then
    if run.snd ∈ life then if q run.snd = q run.fst then .total else .qualitativeBeginning
    else .existentialBeginning
  else if run.snd ∈ life then .existentialEnd else .nonPersistence

theorem ofLifespan_eq_nonPersistence_iff :
    ofLifespan life run q = .nonPersistence ↔ run.fst ∉ life ∧ run.snd ∉ life := by
  unfold ofLifespan; split_ifs <;> simp_all

theorem ofLifespan_eq_existentialEnd_iff :
    ofLifespan life run q = .existentialEnd ↔ run.fst ∉ life ∧ run.snd ∈ life := by
  unfold ofLifespan; split_ifs <;> simp_all

theorem ofLifespan_eq_existentialBeginning_iff :
    ofLifespan life run q = .existentialBeginning ↔ run.fst ∈ life ∧ run.snd ∉ life := by
  unfold ofLifespan; split_ifs <;> simp_all

theorem ofLifespan_eq_qualitativeBeginning_iff :
    ofLifespan life run q = .qualitativeBeginning ↔
      run.fst ∈ life ∧ run.snd ∈ life ∧ q run.snd ≠ q run.fst := by
  unfold ofLifespan; split_ifs <;> simp_all

theorem ofLifespan_eq_total_iff :
    ofLifespan life run q = .total ↔
      run.fst ∈ life ∧ run.snd ∈ life ∧ q run.snd = q run.fst := by
  unfold ofLifespan; split_ifs <;> simp_all

/-! ### The features of the level

The level's features are the persistence features the participant has. -/

@[simp] theorem existsAtBeginning_mem_ofLifespan :
    .existsAtBeginning ∈ ofLifespan life run q ↔ run.fst ∈ life := by
  unfold ofLifespan; split_ifs <;> simp_all <;> decide

@[simp] theorem existsAtEnd_mem_ofLifespan :
    .existsAtEnd ∈ ofLifespan life run q ↔ run.snd ∈ life := by
  unfold ofLifespan; split_ifs <;> simp_all <;> decide

@[simp] theorem qualitiesAtBeginning_mem_ofLifespan :
    .qualitiesAtBeginning ∈ ofLifespan life run q ↔ run.fst ∈ life := by
  unfold ofLifespan; split_ifs <;> simp_all <;> decide

/-- A participant keeps its qualities to the end of the event when it exists there with the
qualities it had at the beginning, if it existed then. -/
@[simp] theorem qualitiesAtEnd_mem_ofLifespan : .qualitiesAtEnd ∈ ofLifespan life run q ↔
    run.snd ∈ life ∧ (run.fst ∈ life → q run.snd = q run.fst) := by
  unfold ofLifespan; split_ifs <;> simp_all <;> decide

/-- A participant is at existential persistence (beginning) or above exactly when it exists when
the event begins. -/
theorem existentialBeginning_le_ofLifespan_iff :
    .existentialBeginning ≤ ofLifespan life run q ↔ run.fst ∈ life :=
  existsAtBeginning_mem_iff_le.symm.trans existsAtBeginning_mem_ofLifespan

theorem fst_lt_of_ofLifespan_eq_existentialEnd (h : ofLifespan life run q = .existentialEnd) :
    run.fst < life.fst :=
  have ⟨hB, hE⟩ := ofLifespan_eq_existentialEnd_iff.1 h
  (NonemptyInterval.notMem_iff.1 hB).resolve_right (run.fst_le_snd.trans hE.2).not_gt

/-- A participant created in an event, existing at its end but not at its beginning, does not
pre-exist it ([grimm-2011] (5)). -/
theorem not_preExists_of_ofLifespan_eq_existentialEnd {X : Type*} {σ : X → NonemptyInterval T}
    {x : X} (h : ofLifespan (σ x) run q = .existentialEnd) :
    ¬ Event.PreExists σ (· = x) run := by
  rw [Event.preExists_eq_iff, not_lt]
  exact (fst_lt_of_ofLifespan_eq_existentialEnd h).le

/-- A participant destroyed in an event, existing at its beginning but not at its end, goes out of
existence before the event ends. -/
theorem snd_lt_of_ofLifespan_eq_existentialBeginning
    (h : ofLifespan life run q = .existentialBeginning) :
    life.snd < run.snd :=
  have ⟨hB, hE⟩ := ofLifespan_eq_existentialBeginning_iff.1 h
  (NonemptyInterval.notMem_iff.1 hE).resolve_left (hB.1.trans run.fst_le_snd).not_gt

/-- A table that comes into existence on day `2` during a building from day `1` to day `3` is
created. -/
example : ofLifespan (⟨(2, 9), by decide⟩ : NonemptyInterval ℤ) ⟨(1, 3), by decide⟩
    (fun _ ↦ ()) = .existentialEnd := by
  decide

end ArgumentStructure.Persistence
