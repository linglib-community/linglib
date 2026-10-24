module

public import Linglib.Semantics.ArgumentStructure.AgentivityLattice.Persistence
public import Linglib.Semantics.Events.Lifespan

/-!
# Persistence from life spans

Grimm's persistence features say whether a participant exists, and keeps its qualities, at the
beginning and at the end of an event. Given the participant's life span, the event's run time and
the participant's qualities over time, each feature holds or fails. The features that hold satisfy
Grimm's exclusion principles, so they make up a persistence level, and each level is the one
Grimm's description of it names. A created participant, existing at the end of the event but not
at the beginning, does not pre-exist the event, and a destroyed one goes out of existence before
the event ends.

## Main definitions

* `PersistenceLevel.Feature.Holds`: a persistence feature holds of a participant in an event.
* `PersistenceLevel.ofLifespan`: the persistence level of a participant in an event, whose features
  are those that hold.

## Main statements

* `PersistenceLevel.valid_holds`: the features that hold satisfy Grimm's exclusion principles.
* `PersistenceLevel.ofLifespan_eq_exPersEnd_iff` and its siblings: Grimm's descriptions of the five
  levels.
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

/-- Grimm's exclusion principles hold of the persistence features of every participant. -/
theorem valid_holds : Valid (Finset.univ.filter (Feature.Holds · life run q)) := by
  simp only [Valid, Finset.mem_filter, Finset.mem_univ, true_and, Feature.Holds]
  tauto

/-- The persistence level of a participant with life span `life` and qualities `q` in an event with
run time `run`, the level whose features are those that hold. -/
def ofLifespan (life run : NonemptyInterval T) (q : T → Q) : PersistenceLevel :=
  featuresOrderIso.symm ⟨Finset.univ.filter (Feature.Holds · life run q), valid_holds⟩

theorem mem_ofLifespan_iff {f : Feature} : f ∈ ofLifespan life run q ↔ f.Holds life run q := by
  simp [← mem_features, ofLifespan]

theorem ofLifespan_eq_iff {l : PersistenceLevel} :
    ofLifespan life run q = l ↔ ∀ f, f.Holds life run q ↔ f ∈ l :=
  ⟨fun h _ ↦ h ▸ mem_ofLifespan_iff.symm,
    fun h ↦ SetLike.ext fun _ ↦ mem_ofLifespan_iff.trans (h _)⟩

/-! ### Grimm's descriptions of the levels -/

theorem ofLifespan_eq_totalNonPersistence_iff :
    ofLifespan life run q = .totalNonPersistence ↔ run.fst ∉ life ∧ run.snd ∉ life := by
  simp [ofLifespan_eq_iff, Feature.forall, Feature.Holds, ← mem_features, features]
  tauto

theorem ofLifespan_eq_exPersEnd_iff :
    ofLifespan life run q = .exPersEnd ↔ run.fst ∉ life ∧ run.snd ∈ life := by
  simp [ofLifespan_eq_iff, Feature.forall, Feature.Holds, ← mem_features, features]
  tauto

theorem ofLifespan_eq_exPersBeginning_iff :
    ofLifespan life run q = .exPersBeginning ↔ run.fst ∈ life ∧ run.snd ∉ life := by
  simp [ofLifespan_eq_iff, Feature.forall, Feature.Holds, ← mem_features, features]
  tauto

theorem ofLifespan_eq_quPersBeginning_iff :
    ofLifespan life run q = .quPersBeginning ↔
      run.fst ∈ life ∧ run.snd ∈ life ∧ q run.snd ≠ q run.fst := by
  simp [ofLifespan_eq_iff, Feature.forall, Feature.Holds, ← mem_features, features]
  tauto

theorem ofLifespan_eq_totalPersistence_iff :
    ofLifespan life run q = .totalPersistence ↔
      run.fst ∈ life ∧ run.snd ∈ life ∧ q run.snd = q run.fst := by
  simp [ofLifespan_eq_iff, Feature.forall, Feature.Holds, ← mem_features, features]
  tauto

/-! ### Existence at the boundaries -/

/-- A participant is at existential persistence (beginning) or above exactly when it exists when
the event begins. -/
theorem exPersBeginning_le_ofLifespan_iff :
    .exPersBeginning ≤ ofLifespan life run q ↔ run.fst ∈ life := by
  rw [le_iff_features_subset, show exPersBeginning.features = {.exPB, .quPB} from rfl]
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, mem_features,
    mem_ofLifespan_iff, Feature.Holds, and_self]

theorem fst_lt_of_ofLifespan_eq_exPersEnd (h : ofLifespan life run q = .exPersEnd) :
    run.fst < life.fst :=
  have ⟨hB, hE⟩ := ofLifespan_eq_exPersEnd_iff.1 h
  (NonemptyInterval.notMem_iff.1 hB).resolve_right (run.fst_le_snd.trans hE.2).not_gt

/-- A participant created in an event, existing at its end but not at its beginning, does not
pre-exist it ([grimm-2011] (5)). -/
theorem not_preExists_of_ofLifespan_eq_exPersEnd {X : Type*} {σ : X → NonemptyInterval T} {x : X}
    (h : ofLifespan (σ x) run q = .exPersEnd) : ¬ Event.PreExists σ (· = x) run := by
  rw [Event.preExists_eq_iff, not_lt]
  exact (fst_lt_of_ofLifespan_eq_exPersEnd h).le

/-- A participant destroyed in an event, existing at its beginning but not at its end, goes out of
existence before the event ends. -/
theorem snd_lt_of_ofLifespan_eq_exPersBeginning (h : ofLifespan life run q = .exPersBeginning) :
    life.snd < run.snd :=
  have ⟨hB, hE⟩ := ofLifespan_eq_exPersBeginning_iff.1 h
  (NonemptyInterval.notMem_iff.1 hE).resolve_left (hB.1.trans run.fst_le_snd).not_gt

/-- A table that comes into existence on day `2` during a building from day `1` to day `3` is
created. -/
example : ofLifespan (⟨(2, 9), by decide⟩ : NonemptyInterval ℤ) ⟨(1, 3), by decide⟩
    (fun _ ↦ ()) = .exPersEnd :=
  ofLifespan_eq_exPersEnd_iff.2 ⟨by decide, by decide⟩

end ArgumentStructure.PersistenceLevel
