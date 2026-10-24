module

public import Linglib.Semantics.ArgumentStructure.AgentivityLattice.Persistence
public import Linglib.Semantics.Events.Lifespan

/-!
# Persistence from life spans

Grimm's persistence features say whether a participant exists, and keeps its qualities, at the
beginning and at the end of an event. Given the participant's life span, the event's run time and
the participant's qualities over time, each feature holds or fails, and the features that hold are
those of the persistence level that Grimm's description of the levels assigns. A created
participant, existing at the end of the event but not at the beginning, does not pre-exist the
event, and a destroyed one goes out of existence before the event ends.

## Main definitions

* `PersistenceLevel.Feature.Holds`: a persistence feature holds of a participant in an event.
* `PersistenceLevel.ofLifespan`: the persistence level of a participant in an event.

## Main statements

* `PersistenceLevel.mem_ofLifespan_iff`: the features of that level are those that hold.
* `PersistenceLevel.valid_holds`: the features that hold satisfy Grimm's exclusion principles.
* `PersistenceLevel.exPersBeginning_le_ofLifespan_iff`: a participant is at existential persistence
  (beginning) or above exactly when it exists when the event begins.
* `PersistenceLevel.not_preExists_of_ofLifespan_eq_exPersEnd`: a created participant does not
  pre-exist the event.
* `PersistenceLevel.snd_lt_of_ofLifespan_eq_exPersBeginning`: a destroyed participant goes out of
  existence before the event ends.

## Implementation notes

A participant persists existentially at a boundary of the event when the boundary lies in its life
span. Its qualities are a function `q` of times. It persists qualitatively at the beginning when it
exists there, and at the end when it exists there with the qualities it had at the beginning, if it
existed then; this is the reading under which Grimm's exclusion principles hold of every
participant. Only the boundaries of the event are compared, so a quality that changes and changes
back counts as persisting. A predicate's persistence level for an argument, the features it entails
for every participant, is not formalized.

## References

* [grimm-2011]
-/

@[expose] public section

namespace ArgumentStructure.PersistenceLevel

variable {T Q : Type*} [LinearOrder T] {life run : NonemptyInterval T} {q : T → Q}

/-- The persistence feature `f` holds of a participant with life span `life` and qualities `q` in
an event with run time `run`. -/
def Feature.Holds (f : Feature) (life run : NonemptyInterval T) (q : T → Q) : Prop :=
  match f with
  | .exPB | .quPB => run.fst ∈ life
  | .exPE => run.snd ∈ life
  | .quPE => run.snd ∈ life ∧ (run.fst ∈ life → q run.snd = q run.fst)

instance [DecidableEq Q] : DecidablePred (Feature.Holds · life run q) := fun f ↦ by
  cases f <;> unfold Feature.Holds <;> infer_instance

variable [DecidableEq Q]

/-- The persistence level of a participant with life span `life` and qualities `q` in an event with
run time `run`, by Grimm's descriptions: a participant existing at neither end does not persist,
one existing only at the beginning or only at the end persists existentially there, and one
existing at both ends persists totally or only at the beginning as its qualities are unchanged or
not ([grimm-2011] pp. 524–525). -/
def ofLifespan (life run : NonemptyInterval T) (q : T → Q) : PersistenceLevel :=
  if run.fst ∈ life then
    if run.snd ∈ life then if q run.snd = q run.fst then .totalPersistence else .quPersBeginning
    else .exPersBeginning
  else if run.snd ∈ life then .exPersEnd else .totalNonPersistence

/-- The features of a participant's persistence level are the features that hold of it. -/
theorem mem_ofLifespan_iff {f : Feature} : f ∈ ofLifespan life run q ↔ f.Holds life run q := by
  rw [← mem_features]
  unfold ofLifespan
  split_ifs <;> cases f <;> simp_all [features, Feature.Holds]

/-- Grimm's exclusion principles hold of the persistence features of every participant. -/
theorem valid_holds : Valid (Finset.univ.filter (Feature.Holds · life run q)) := by
  have : Finset.univ.filter (Feature.Holds · life run q) = (ofLifespan life run q).features := by
    ext; simp [mem_ofLifespan_iff]
  rw [this, ← Set.mem_ofPred_eq (p := Valid), ← range_features]
  exact ⟨_, rfl⟩

/-- A participant is at existential persistence (beginning) or above exactly when it exists when
the event begins. -/
theorem exPersBeginning_le_ofLifespan_iff :
    .exPersBeginning ≤ ofLifespan life run q ↔ run.fst ∈ life := by
  rw [le_iff_features_subset, show exPersBeginning.features = {.exPB, .quPB} from rfl]
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, mem_features,
    mem_ofLifespan_iff, Feature.Holds, and_self]

theorem fst_lt_of_ofLifespan_eq_exPersEnd (h : ofLifespan life run q = .exPersEnd) :
    run.fst < life.fst := by
  have hB : ¬ Feature.exPB.Holds life run q := fun hB ↦
    absurd (mem_ofLifespan_iff.2 hB) (by rw [h]; decide)
  have hE : Feature.exPE.Holds life run q := mem_ofLifespan_iff.1 (by rw [h]; decide)
  exact lt_of_not_ge fun h' ↦ hB ⟨h', run.fst_le_snd.trans hE.2⟩

/-- A participant created in an event, existing at its end but not at its beginning, does not
pre-exist it ([grimm-2011] (5)). -/
theorem not_preExists_of_ofLifespan_eq_exPersEnd {X : Type*} {σ : X → NonemptyInterval T} {x : X}
    (h : ofLifespan (σ x) run q = .exPersEnd) : ¬ Event.PreExists σ (· = x) run := by
  rw [Event.preExists_eq_iff, not_lt]
  exact (fst_lt_of_ofLifespan_eq_exPersEnd h).le

/-- A participant destroyed in an event, existing at its beginning but not at its end, goes out of
existence before the event ends. -/
theorem snd_lt_of_ofLifespan_eq_exPersBeginning (h : ofLifespan life run q = .exPersBeginning) :
    life.snd < run.snd := by
  have hB : Feature.exPB.Holds life run q := mem_ofLifespan_iff.1 (by rw [h]; decide)
  have hE : ¬ Feature.exPE.Holds life run q := fun hE ↦
    absurd (mem_ofLifespan_iff.2 hE) (by rw [h]; decide)
  exact lt_of_not_ge fun h' ↦ hE ⟨hB.1.trans run.fst_le_snd, h'⟩

/-- A table that comes into existence on day `2` during a building from day `1` to day `3` is
created. -/
example : ofLifespan (⟨(2, 9), by decide⟩ : NonemptyInterval ℤ) ⟨(1, 3), by decide⟩
    (fun _ ↦ ()) = .exPersEnd := by
  decide

end ArgumentStructure.PersistenceLevel
