module

public import Linglib.Semantics.Questions.Partition.Basic
public import Linglib.Semantics.ArgumentStructure.LevinClass.Basic
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Data.Examples.LuPanDegen2025

/-!
# Lu, Pan and Degen (2025): Evidence for a Discourse Account of Manner-of-Speaking Islands

This file formalizes the backgroundedness account of manner-of-speaking islands that
Lu, Pan and Degen support in five acceptability experiments. A constituent is foregrounded
when its alternatives are among the answers to the question under discussion, (3), with
alternative sets and answers after Roberts, and backgrounded otherwise
(`Foregrounded`), which is the question deciding each of the constituent's alternatives
(`Setoid.le_ker_iff_forall_decides`). A communication event has a manner and a content,
and the manner question backgrounds the content (`mannerQUD`, `contentQUD`,
`not_foregrounded_content_mannerQUD`). Movement foregrounds the moved element, so moving it out of
a backgrounded complement is the information-structural clash of Erteschik-Shir: the
embedded object is an island exactly when the complement is backgrounded under the question under
discussion (`Island`).

Prosodic focus sets that question, focus on the matrix predicate raising the manner question and
focus on the embedded object the content question. Without focus the predicate sets it: a
manner-of-speaking verb carries a manner component, *whisper* being *say* in a whispering manner,
which makes the manner question the default, while the light *say* leaves the content question
(`activeQUD`, `island_iff`). The experiments' findings follow for each predicate: embedded focus
removes the island of a manner-of-speaking verb, Experiment 1 (`island_whisper_iff`); focus on
*say* creates one, Experiment 2a (`island_say_iff`); and a manner adverb makes *say* behave as a
manner-of-speaking verb, by default in Experiment 3a and under focus in 3b
(`island_sayAdverb_iff_island_whisper`). The manner component is read from the verb's Levin class in
`Fragments/English` (`MatrixPredicate.hasManner_of_mannerOfSpeaking`,
`MatrixPredicate.hasManner_say_iff`).

## Implementation notes

(3) asks the alternatives relative to a constituent to be among the complete answers to the
question. Over partition questions, whose cells are the complete answers, this is rendered as
the question settling the constituent: two events in one cell agree on it, so the question
decides each of its alternatives. The paper takes one question to be under discussion at a time,
which is why focus overrides the predicate's default.

The negation test (7) of earlier work is not formalized: the paper counts it a test of
projection, correlated with backgroundedness but distinct from it, and probes the embedded
object's backgroundedness with a comprehension task instead. The subjacency and
verb-frame-frequency accounts the paper argues against are described in prose: prosodic focus
changes neither structure nor frequency, and the *say* plus adverb contrast holds the verb
constant. The residual difference between manner-of-speaking verbs and *say* under one prosody
in Experiment 2a, the default backgroundedness contrast of Experiment 2b, and the rating means
are not represented; the paper notes that the account makes no prediction about the obligatory
overt complementizer of manner-of-speaking complements (22).

## TODO

The stimuli of `Data/Examples/LuPanDegen2025` are printed unmarked; which member of each contrast
is degraded is a rating result of the experiments, for `Data/Experiments`, and the island rule
is not yet checked against those results.

## References

* [lu-pan-degen-2025]
* [roberts-1996]
* [roberts-2012]
* [erteschik-shir-1973]
* [levin-1993]
-/

@[expose] public section

namespace LuPanDegen2025

open ArgumentStructure English English.Verbs

/-! ### Foregrounding (3) -/

section Foregrounding

variable {M A : Type*}

/-- A dimension `π` of the events is foregrounded under the question `q`, (3): its alternatives
are among the answers, so two events in one cell agree on it. A dimension that is not
foregrounded is backgrounded. -/
def Foregrounded (q : Setoid M) (π : M → A) : Prop :=
  q ≤ Setoid.ker π

end Foregrounding

/-! ### Communication events -/

/-- A communication event: how it was said and what was said. -/
structure CommEvent (Manner Content : Type*) where
  /-- How it was said. -/
  manner : Manner
  /-- What was said. -/
  content : Content

section Questions

variable {Manner Content : Type*}

/-- The manner question, *how did John say it?*: events in one cell share a manner. -/
def mannerQUD : Setoid (CommEvent Manner Content) := Setoid.ker CommEvent.manner

/-- The content question, *what did John say?*: events in one cell share a content. -/
def contentQUD : Setoid (CommEvent Manner Content) := Setoid.ker CommEvent.content

theorem foregrounded_manner_mannerQUD :
    Foregrounded (mannerQUD (Manner := Manner) (Content := Content)) CommEvent.manner :=
  le_rfl

theorem foregrounded_content_contentQUD :
    Foregrounded (contentQUD (Manner := Manner) (Content := Content)) CommEvent.content :=
  le_rfl

theorem not_foregrounded_content_mannerQUD [Nonempty Manner] [Nontrivial Content] :
    ¬ Foregrounded (mannerQUD (Manner := Manner) (Content := Content)) CommEvent.content := by
  obtain ⟨m⟩ := ‹Nonempty Manner›
  obtain ⟨c, c', h⟩ := exists_pair_ne Content
  exact fun hf ↦ h (hf (x := ⟨m, c⟩) (y := ⟨m, c'⟩) rfl)

end Questions

/-! ### The question under discussion and the island -/

/-- The matrix predicate: a verb of the fragment, and whether a manner adverb modifies it. -/
structure MatrixPredicate where
  /-- The matrix verb. -/
  verb : English.Verbs.Verb
  /-- Whether a manner adverb modifies the verb. -/
  mannerAdverb : Bool

namespace MatrixPredicate

/-- The predicate carries a manner component, as a manner-of-speaking verb of [levin-1993] or
by a manner adverb. -/
def HasManner (p : MatrixPredicate) : Prop :=
  .mannerOfSpeaking ∈ p.verb.levinClasses ∨ p.mannerAdverb = true

instance : DecidablePred HasManner := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

theorem hasManner_of_mannerOfSpeaking {v : English.Verbs.Verb}
    (h : .mannerOfSpeaking ∈ v.levinClasses) (b : Bool) : HasManner ⟨v, b⟩ :=
  .inl h

theorem hasManner_say_iff {v : English.Verbs.Verb} (h : v.levinClasses = {.say}) (b : Bool) :
    HasManner ⟨v, b⟩ ↔ b = true := by
  simp [HasManner, h]

end MatrixPredicate

/-- Where the context puts prosodic focus: on the matrix predicate, its verb or its manner
adverb, on the embedded object, or nowhere. -/
inductive FocusCondition where
  | predicate
  | embedded
  | unmarked
  deriving DecidableEq

section Island

variable (Manner Content : Type*)

/-- The question under discussion: focus on the predicate raises the manner question, the
alternatives of a verb of saying being its manners, and focus on the embedded object the content
question; without focus a predicate with a manner component raises the manner question and the
light *say* the content question. -/
def activeQUD (p : MatrixPredicate) : FocusCondition → Setoid (CommEvent Manner Content)
  | .predicate => mannerQUD
  | .embedded => contentQUD
  | .unmarked => if p.HasManner then mannerQUD else contentQUD

/-- The embedded object is an island when the complement is backgrounded under the question
under discussion: movement foregrounds the moved element, which clashes with the backgrounded
complement it leaves ([erteschik-shir-1973]). -/
def Island (p : MatrixPredicate) (f : FocusCondition) : Prop :=
  ¬ Foregrounded (activeQUD Manner Content p f) CommEvent.content

variable {Manner Content}

theorem not_island_embedded (p : MatrixPredicate) : ¬ Island Manner Content p .embedded :=
  fun h ↦ h le_rfl

variable [Nonempty Manner] [Nontrivial Content]

theorem island_iff (p : MatrixPredicate) (f : FocusCondition) :
    Island Manner Content p f ↔ f = .predicate ∨ f = .unmarked ∧ p.HasManner := by
  cases f
  · simpa [Island, activeQUD] using not_foregrounded_content_mannerQUD
  · simpa [Island, activeQUD] using foregrounded_content_contentQUD
  · by_cases h : p.HasManner <;>
      simp [Island, activeQUD, h, not_foregrounded_content_mannerQUD,
        foregrounded_content_contentQUD]

theorem island_whisper_iff (f : FocusCondition) :
    Island Manner Content ⟨whisper, false⟩ f ↔ f ≠ .embedded := by
  have := MatrixPredicate.hasManner_of_mannerOfSpeaking (v := whisper) (by decide) false
  cases f <;> simp [island_iff, this]

theorem island_say_iff (f : FocusCondition) :
    Island Manner Content ⟨say, false⟩ f ↔ f = .predicate := by
  have := MatrixPredicate.hasManner_say_iff (v := say) (by decide) false
  cases f <;> simp [island_iff, this]

theorem island_sayAdverb_iff_island_whisper (f : FocusCondition) :
    Island Manner Content ⟨say, true⟩ f ↔ Island Manner Content ⟨whisper, false⟩ f := by
  have := (MatrixPredicate.hasManner_say_iff (v := say) (by decide) true).2 rfl
  rw [island_whisper_iff]
  cases f <;> simp [island_iff, this]

/-! ### The stimulus rows -/

/-- The matrix predicate of a stimulus row: *whisper* for the manner-of-speaking items,
*say* and *say softly* for the others. -/
def rowPredicate (e : Datum) : Option MatrixPredicate :=
  match e.feature? "verb_type" with
  | some "mos" => some ⟨whisper, false⟩
  | some "say" => some ⟨say, false⟩
  | some "sayAdverb" => some ⟨say, true⟩
  | _ => none

/-- The focus condition of a stimulus row. -/
def rowFocus (e : Datum) : Option FocusCondition :=
  match e.feature? "focus_condition" with
  | some "verbFocus" | some "adverbFocus" => some .predicate
  | some "embeddedFocus" => some .embedded
  | some "none" => some .unmarked
  | _ => none

theorem rows_parse : ∀ e ∈ Examples.all, (rowPredicate e).isSome ∧ (rowFocus e).isSome := by
  decide

end Island

end LuPanDegen2025
