module

public import Linglib.Semantics.ArgumentStructure.ThematicRole
public import Linglib.Discourse.Commitment.Table
public import Linglib.Discourse.Role
public import Linglib.Syntax.Clause.Basic
public import Linglib.Data.Examples.Rudin2025b

/-!
# Rudin (2025): Embedded Intonation and Quotative Complements to Verbs of Speech

Rudin gives a double-Davidsonian semantics for quotative complements to verbs of speech and
applies it to embedded rising declaratives. A quotation is a performance that the report refers
to demonstratively, and the quotative complementizer relates it to the speech event by
reenactment, so *Ayka said "p"* denotes the saying events that the performance reenacts. A verb
of speech is fixed by a meaning postulate over reenactments, so quoting a performance under a
verb is contradictory exactly when the performance lacks the verb's property: karate gestures
under *say*, a whisper under *yell*, a rising declarative under *assert*. A rising declarative
under *ask* is consistent, because its utterance raises an issue without a commitment that could
resolve it, an asking in Farkas and Bruce's Table model, so embedded rising declaratives are no
evidence that rising declaratives denote questions.

## Main definitions

* `speechVerb`: a verb of speech under the paper's meaning-postulate template.
* `quoteReport`: a quotative speech report.
* `Performance.Asking`: a performance that raises an issue without commitment.

## Implementation notes

Reenactment is a relation from events to performances, and the model is left free: a
quotative report is consistent when some reenactment relation makes it true. A performance is
its linguistic material, none for karate gestures, inarticulate for a howl or a random string,
or the utterance of a sentence with its clause type, radical and tune, together with its
volume. Its context update is the paper's: a falling declarative is a default assertion, a
rising declarative places its proposition on the Table without commitment, and an
interrogative is a default polar question. Askings and assertions are the paper's
configurations of these primitives, quantified over contexts. The paper states the postulates
for *say* and *ask*; the properties for *yell*, *whisper*, *assert* and *claim* are the ones
its discussion of those verbs invokes. Interrogative grunts, which the paper takes to raise an
issue without uttering a sentence, are not represented.

## References

* [rudin-2025b]
* [farkas-bruce-2010]
* [clark-gerrig-1990]
* [davidson-1979]
* [davidson-2015]
* [hacquard-2010]
* [farkas-roelofsen-2017]
-/

@[expose] public section

namespace Rudin2025b

open ArgumentStructure Commitment

variable {E P δ W : Type*}

/-! ### Quotative and ordinary complements -/

/-- A verb of speech under the paper's template holds of an event exactly when every performance
reenacting it has the verb's characteristic property. -/
def speechVerb (reenact : E → P → Prop) (prop : P → Prop) (e : E) : Prop :=
  ∀ u, reenact e u → prop u

/-- The quotative complementizer holds of the events that the performance reenacts. -/
def quote (reenact : E → P → Prop) (u : P) (e : E) : Prop := reenact e u

/-- An ordinary clausal complement holds of the events whose content is the clause's denotation. -/
def thatClause (content : E → δ → Prop) (d : δ) (e : E) : Prop := content e d

/-- A quotative speech report holds, by predicate modification, of the verb's events that the
performance reenacts. -/
def quoteReport (reenact : E → P → Prop) (prop : P → Prop) (u : P) (e : E) : Prop :=
  speechVerb reenact prop e ∧ quote reenact u e

theorem not_quoteReport {reenact : E → P → Prop} {prop : P → Prop} {u : P} (h : ¬ prop u)
    (e : E) : ¬ quoteReport reenact prop u e :=
  λ ⟨hv, hr⟩ => h (hv u hr)

/-- With the reenactment relation free, a quotative report of an event is satisfiable exactly
when the performance has the verb's property. -/
theorem exists_reenact_iff (prop : P → Prop) (u : P) (e : E) :
    (∃ reenact : E → P → Prop, quoteReport reenact prop u e) ↔ prop u :=
  ⟨λ ⟨_, hv, hr⟩ => hv u hr, λ h => ⟨λ _ v => v = u, λ _ hv => hv ▸ h, rfl⟩⟩

/-- A sortal restriction on content requires the content of every event of the verb to have the
sort. -/
def ContentSort (V : E → Prop) (content : E → δ → Prop) (sort : δ → Prop) : Prop :=
  ∀ e d, V e → content e d → sort d

theorem not_thatClause {V : E → Prop} {content : E → δ → Prop} {sort : δ → Prop}
    (hV : ContentSort V content sort) {d : δ} (hd : ¬ sort d) (e : E) :
    ¬ (V e ∧ thatClause content d e) :=
  λ ⟨hv, hc⟩ => hd (hV e d hv hc)

/-! ### Performances and their context updates -/

/-- A `Volume` is the volume of a vocalization. -/
inductive Volume where
  | neutral
  | loud
  | whispered
  deriving DecidableEq

/-- A `Sentence` records an uttered sentence's clause type, the denotation of its radical, and its
tune. -/
structure Sentence (W : Type*) where
  type : Clause.SentenceType
  radical : Set W
  rising : Bool

/-- The linguistic material of a performance is none, inarticulate material, or the utterance of a
sentence. -/
inductive Material (W : Type*) where
  | none
  | inarticulate
  | utterance (s : Sentence W)

/-- A performance consists of its linguistic material and its volume. -/
structure Performance (W : Type*) where
  material : Material W
  volume : Volume

/-- Material is linguistic when it produces linguistic material. -/
def Material.Linguistic : Material W → Prop
  | .none => False
  | _ => True

/-- Material is response-eliciting when it is a rising declarative or an interrogative. -/
def Material.Resp : Material W → Prop
  | .utterance s => s.type = .declarative ∧ s.rising = true ∨ s.type = .polar
  | _ => False

/-- Material is assertive when it is a falling declarative. -/
def Material.Assertive : Material W → Prop
  | .utterance s => s.type = .declarative ∧ s.rising = false
  | _ => False

instance : DecidablePred (Material.Linguistic (W := W)) := λ m => by
  cases m <;> unfold Material.Linguistic <;> infer_instance

instance : DecidablePred (Material.Resp (W := W)) := λ m => by
  cases m <;> unfold Material.Resp <;> infer_instance

instance : DecidablePred (Material.Assertive (W := W)) := λ m => by
  cases m <;> unfold Material.Assertive <;> infer_instance

/-- In the context update of an uttered sentence, a falling declarative is a default assertion, a
rising declarative only places its proposition on the Table, and an interrogative is a default
polar question. -/
def Sentence.update : Sentence W → Table Discourse.Role W → Table Discourse.Role W
  | ⟨.declarative, p, false⟩, K => K.assert .speaker p
  | ⟨.declarative, p, true⟩, K => K.push (Question.ofSet p)
  | ⟨.polar, p, _⟩, K => K.polarQuestion p
  | _, K => K

/-- The context update of a performance is that of the sentence it utters, if any. -/
def Performance.update : Performance W → Table Discourse.Role W → Table Discourse.Role W
  | ⟨.utterance s, _⟩, K => s.update K
  | _, K => K

/-- A performance is an asking when in every context it raises an issue without committing
its speaker to any alternative of that issue. -/
def Performance.Asking (u : Performance W) : Prop :=
  ∀ K : Table Discourse.Role W, ∃ i, (u.update K).stack = i :: K.stack ∧
    ∀ q ∈ Question.alt i,
      q ∈ (u.update K).discourseCommitments .speaker → q ∈ K.discourseCommitments .speaker

/-- A performance is an assertion when in every context it raises an issue with a single
alternative and commits its speaker to it. -/
def Performance.Assertion (u : Performance W) : Prop :=
  ∀ K : Table Discourse.Role W, ∃ q, (u.update K).stack = Question.ofSet q :: K.stack ∧
    q ∈ (u.update K).discourseCommitments .speaker

private theorem not_asking_of_stack {u : Performance W}
    (h : ∀ K : Table Discourse.Role W, (u.update K).stack = K.stack) : ¬ u.Asking :=
  λ ha => let ⟨i, hi, _⟩ := ha Table.empty; List.cons_ne_nil i [] ((h _).symm.trans hi).symm

private theorem not_assertion_of_stack {u : Performance W}
    (h : ∀ K : Table Discourse.Role W, (u.update K).stack = K.stack) : ¬ u.Assertion :=
  λ ha => let ⟨q, hi, _⟩ := ha Table.empty
    List.cons_ne_nil (Question.ofSet q) [] ((h _).symm.trans hi).symm

/-- A performance is an asking exactly when it utters a rising declarative or an
interrogative. -/
theorem Performance.asking_iff : ∀ u : Performance W, u.Asking ↔ u.material.Resp
  | ⟨.none, _⟩ | ⟨.inarticulate, _⟩ => iff_of_false (not_asking_of_stack λ _ => rfl) id
  | ⟨.utterance ⟨.declarative, p, false⟩, _⟩ =>
    iff_of_false (λ h => by
      obtain ⟨i, hi, hq⟩ := h Table.empty
      simp only [Performance.update, Sentence.update, Table.stack_assert, Table.stack_empty,
        List.cons.injEq, and_true] at hi
      subst hi
      have h₁ : p ∈ (Table.empty.assert Discourse.Role.speaker p).discourseCommitments .speaker :=
        Table.mem_discourseCommitments_assert _ _ _
      simpa using hq p (by simp) h₁)
      (by simp [Material.Resp])
  | ⟨.utterance ⟨.declarative, p, true⟩, _⟩ =>
    iff_of_true (λ _ => ⟨Question.ofSet p, rfl, λ _ _ hq => hq⟩) (Or.inl ⟨rfl, rfl⟩)
  | ⟨.utterance ⟨.polar, p, _⟩, _⟩ =>
    iff_of_true (λ _ => ⟨Question.polar p, rfl, λ _ _ hq => hq⟩) (Or.inr rfl)
  | ⟨.utterance ⟨.alternative, _, _⟩, _⟩ | ⟨.utterance ⟨.constituent, _, _⟩, _⟩
  | ⟨.utterance ⟨.imperative, _, _⟩, _⟩ | ⟨.utterance ⟨.promissive, _, _⟩, _⟩
  | ⟨.utterance ⟨.exclamative, _, _⟩, _⟩ =>
    iff_of_false (not_asking_of_stack λ _ => rfl) (by simp [Material.Resp])

theorem Performance.assertion_iff : ∀ u : Performance W, u.Assertion ↔ u.material.Assertive
  | ⟨.none, _⟩ | ⟨.inarticulate, _⟩ => iff_of_false (not_assertion_of_stack λ _ => rfl) id
  | ⟨.utterance ⟨.declarative, p, false⟩, _⟩ =>
    iff_of_true (λ K => ⟨p, rfl, Table.mem_discourseCommitments_assert K .speaker p⟩)
      ⟨rfl, rfl⟩
  | ⟨.utterance ⟨.declarative, _, true⟩, _⟩ =>
    iff_of_false (λ h => by
      obtain ⟨_, _, hq⟩ := h Table.empty
      simp [Performance.update, Sentence.update] at hq) (by simp [Material.Assertive])
  | ⟨.utterance ⟨.polar, _, _⟩, _⟩ =>
    iff_of_false (λ h => by
      obtain ⟨_, _, hq⟩ := h Table.empty
      simp [Performance.update, Sentence.update] at hq) (by simp [Material.Assertive])
  | ⟨.utterance ⟨.alternative, _, _⟩, _⟩ | ⟨.utterance ⟨.constituent, _, _⟩, _⟩
  | ⟨.utterance ⟨.imperative, _, _⟩, _⟩ | ⟨.utterance ⟨.promissive, _, _⟩, _⟩
  | ⟨.utterance ⟨.exclamative, _, _⟩, _⟩ =>
    iff_of_false (not_assertion_of_stack λ _ => rfl) (by simp [Material.Assertive])

instance (u : Performance W) : Decidable u.Asking := decidable_of_iff _ u.asking_iff.symm

instance (u : Performance W) : Decidable u.Assertion :=
  decidable_of_iff _ u.assertion_iff.symm

theorem Performance.not_asking_of_assertion {u : Performance W} (h : u.Assertion) :
    ¬ u.Asking := by
  rw [assertion_iff] at h
  rw [asking_iff]
  obtain ⟨m, _⟩ := u
  cases m with
  | utterance s => simp only [Material.Assertive, Material.Resp] at h ⊢; simp [h]
  | _ => exact h.elim

/-! ### The verbs of speech -/

/-- A `Verb` is one of the verbs of speech the paper examines, or *wonder*, a species of asking. -/
inductive Verb where
  | say
  | assert
  | claim
  | ask
  | wonder
  | yell
  | shout
  | whisper
  deriving DecidableEq, Repr

/-- `v.property` is the property that the meaning postulate of `v` requires of the performances
reenacting its events,
linguistic material for *say*, an assertion for *assert* and *claim*, an asking for *ask* and
*wonder*, loudness for *yell* and *shout*, a whisper for *whisper*. -/
def Verb.property : Verb → Performance W → Prop
  | .say => λ u => u.material.Linguistic
  | .assert | .claim => Performance.Assertion
  | .ask | .wonder => Performance.Asking
  | .yell | .shout => λ u => u.volume = .loud
  | .whisper => λ u => u.volume = .whispered

instance (v : Verb) (u : Performance W) : Decidable (v.property u) := by
  cases v <;> simp only [Verb.property] <;> infer_instance

variable {reenact : E → Performance W → Prop} {v : Volume} (p : Set W) (e : E)

theorem say_gesture : ¬ quoteReport reenact Verb.say.property ⟨.none, v⟩ e :=
  not_quoteReport id e

theorem yell_whispered (s : Material W) :
    ¬ quoteReport reenact Verb.yell.property ⟨s, .whispered⟩ e :=
  not_quoteReport (by simp [Verb.property]) e

theorem assert_risingDeclarative :
    ¬ quoteReport reenact Verb.assert.property ⟨.utterance ⟨.declarative, p, true⟩, v⟩ e :=
  not_quoteReport (λ h => by simpa [Material.Assertive] using (Performance.assertion_iff _).1 h) e

/-- A rising declarative under *ask* is satisfiable, whatever proposition it denotes, since its
utterance is an asking. -/
theorem ask_risingDeclarative :
    ∃ reenact : E → Performance W → Prop,
      quoteReport reenact Verb.ask.property ⟨.utterance ⟨.declarative, p, true⟩, v⟩ e :=
  (exists_reenact_iff _ _ e).2 ((Performance.asking_iff _).2 (Or.inl ⟨rfl, rfl⟩))

/-! ### The paper's judgments -/

def verbs : List (String × Verb) :=
  [("say", .say), ("assert", .assert), ("claim", .claim), ("ask", .ask), ("wonder", .wonder),
    ("yell", .yell), ("shout", .shout), ("whisper", .whisper)]

def volumes : List (String × Volume) :=
  [("neutral", .neutral), ("loud", .loud), ("whispered", .whispered)]

/-- `types` lists the sentence types the rows record; the paper's interrogatives are polar
questions. -/
def types : List (String × Clause.SentenceType) :=
  [("declarative", .declarative), ("interrogative", .polar)]

/-- `performance? x` is the quoted performance of the row `x`, its sentence read as denoting a fixed
proposition. -/
def performance? (x : Datum) : Option (Performance Bool) := do
  let volume ← x.parse? "volume" volumes
  let material ← match x.feature? "material" with
    | some "none" => some .none
    | some "inarticulate" => some .inarticulate
    | some "sentence" => do
      let type ← x.parse? "mood" types
      let rising ← x.parse? "tune" [("rising", true), ("falling", false)]
      pure (.utterance ⟨type, {true}, rising⟩)
    | _ => none
  pure ⟨material, volume⟩

/-- `datum x` reads the verb of speech and the quoted performance off the row `x`. -/
def datum (x : Datum) : Option (Verb × Performance Bool) := do
  pure (← x.parse? "verb" verbs, ← performance? x)

/-- `data` lists the paper's quotative reports. -/
def data : List (Datum × Verb × Performance Bool) :=
  Examples.all.filterMap λ x => (datum x).map (x, ·)

/-- `e₀` is the one event of the reports. -/
def e₀ : Unit := ()

/-- Each of the paper's quotative reports is judged acceptable exactly when it is satisfiable
under the verb's meaning postulate. -/
theorem judgments : ∀ d ∈ data, d.1.judgment = .acceptable ↔
    ∃ reenact : Unit → Performance Bool → Prop, quoteReport reenact d.2.1.property d.2.2 e₀ := by
  simp only [exists_reenact_iff]
  decide +kernel

end Rudin2025b
