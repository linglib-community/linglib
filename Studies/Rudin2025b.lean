module

public import Linglib.Logic.Modal.Defs
public import Linglib.Discourse.Commitment.Table
public import Linglib.Discourse.Role
public import Linglib.Data.Examples.Rudin2025b
public import Linglib.Data.Examples.Readers

/-!
# Rudin (2025): Embedded Intonation and Quotative Complements to Verbs of Speech

A quotative complement to a verb of speech refers demonstratively to a performance, which the
quotative complementizer relates to the reported event by reenactment; an ordinary clausal
complement relates its denotation to the event by content instead. A verb of speech is a predicate
of events fixed by a meaning postulate over reenactments: an event is a saying exactly when every
performance reenacting it produces linguistic material, so the extension of *say* is necessity
along reenactment of that property, $\Box_{\mathrm{REENACT}}\,\mathrm{LINGMAT}$. A quotative
report is then [consistent exactly when](##exists_report_iff) the performance has the verb's
property: karate gestures under *say* and a whisper under *yell* are contradictions.

Rising declaratives embed only as quotations, so their distribution under *ask* and *assert* shows
what their utterances do rather than what they denote. In Farkas and Bruce's Table model, uttering
a sentence raises its denotation as an issue and, unless the tune is rising, commits the speaker to
the denotation's informative content. An asking raises an issue without a commitment that resolves
it, and an assertion commits the speaker to the single resolution of the issue it raises. A rising
utterance is an asking and never an assertion [whatever it denotes](##report_rising_ask_assert),
so a quoted rising declarative is consistent under *ask* and contradictory under *assert* on the
view that it denotes a proposition and on the view that it denotes a question alike.

## Implementation notes

* Reenactment and content are relations from events, `SetRel`. A postulate of the form
  "$V(e)$ iff every $u$ that $e$ relates to has $Q$" makes the verb's extension `□[R] Q`, so
  consistency is the existence of a reenactment relation that makes the report true.
* An uttered sentence is its denotation, a `Question` (a proposition is `Question.ofSet p`), and
  whether its tune is rising; clause type matters only through the denotation it determines. The
  rows read a declarative as denoting its radical and an interrogative as the polar question on
  it, with the radical a fixed contingent proposition.
* The paper derives its three update tables, for falling and rising declaratives and rising polar
  interrogatives, from the update rule above, and here they are
  [instances of the rule](##utter_ofSet_false). A state resolves an issue when it belongs to it,
  so the falling utterance of a denotation asks exactly when the denotation is inquisitive. That
  is not decidable, so the decision procedure for askings is classical in that case; the rows
  quote no falling utterance under *ask*.
* The paper states the postulates for *say* and *ask*. *Yell* and *whisper* require linguistic
  material at a volume, its "events of linguistic production of a particular kind"; *assert* and
  *claim* require an assertion, the property its discussion of them invokes. Interrogative grunts
  are not represented.

## Errata

* The content postulates (66) and (80) are printed as biconditionals, but the prose glosses only
  the left-to-right direction. Read right to left, (80) makes every event an asking with every
  question as its content, so under (86) every reenactment is an asking and the paper's own (60),
  a quoted falling declarative under *say*, is
  [contradictory](##not_report_say_of_printed). `not_report` uses the left-to-right reading.

## References

* [rudin-2025b]
* [farkas-bruce-2010]
* [farkas-roelofsen-2017]
* [clark-gerrig-1990]
* [davidson-1979]
* [davidson-2015]
* [hacquard-2010]
* [ciardelli-groenendijk-roelofsen-2018]
-/

@[expose] public section

namespace Rudin2025b

open ModalLogic SetRel Commitment Question

variable {E X W : Type*}

/-! ### Speech reports -/

/-- A speech report holds, by predicate modification, of the events of its verb `V` that bear the
thematic relation `θ` to its complement `x`: reenactment by a quoted performance (62), or content
for an ordinary clause (65). -/
def report (V : E → Prop) (θ : SetRel E X) (x : X) (e : E) : Prop := V e ∧ e ~[θ] x

-- (68); with content for reenactment, the left-to-right reading of (66) and (80)
theorem not_report {V : E → Prop} {θ : SetRel E X} {Q : X → Prop} {x : X} (hV : V ≤ □[θ] Q)
    (hx : ¬ Q x) (e : E) : ¬ report V θ x e :=
  fun ⟨he, hθ⟩ ↦ hx (hV e he x hθ)

/-- A report whose verb is fixed by a postulate of the form (59) is consistent, for some
reenactment relation, exactly when its complement has the property the postulate requires. -/
theorem exists_report_iff [Nonempty E] (Q : X → Prop) (x : X) :
    (∃ θ : SetRel E X, ∃ e, report (□[θ] Q) θ x e) ↔ Q x :=
  ⟨fun ⟨_, e, h⟩ ↦ by_contra fun hx ↦ not_report le_rfl hx e h,
    fun hx ↦ ⟨Function.graph fun _ ↦ x, Classical.arbitrary E, by rw [box_graph]; exact hx, rfl⟩⟩

/-! ### Performances and their context updates -/

/-- A `Volume` is the volume of a vocalization. -/
inductive Volume where
  | neutral
  | loud
  | whispered
  deriving DecidableEq

/-- The linguistic material of a performance is none, inarticulate material, or the utterance of a
sentence that denotes `D`, with a rising tune or not. -/
inductive Material (W : Type*) where
  | none
  | inarticulate
  | utterance (D : Question W) (rising : Bool)

/-- A performance consists of its linguistic material and its volume. -/
structure Performance (W : Type*) where
  material : Material W
  volume : Volume

/-- Material is linguistic when there is some. -/
def Material.Linguistic : Material W → Prop
  | .none => False
  | _ => True

instance : DecidablePred (Material.Linguistic (W := W)) := fun m ↦ by
  cases m <;> unfold Material.Linguistic <;> infer_instance

/-- Uttering a sentence that denotes `D` raises `D` as an issue and, unless the tune is rising,
commits the speaker to the informative content of `D`. -/
def utter (D : Question W) : Bool → Table Discourse.Role W → Table Discourse.Role W
  | true, K => K.push D
  | false, K => (K.commit .speaker D.info).push D

-- (83)
theorem utter_ofSet_false (p : Set W) (K : Table Discourse.Role W) :
    utter (ofSet p) false K = K.assert .speaker p := by
  rw [utter, info_ofSet]
  rfl

-- (85)
theorem utter_polar_true (p : Set W) (K : Table Discourse.Role W) :
    utter (polar p) true K = K.polarQuestion p := rfl

/-- The context update of a performance is that of the sentence it utters, if any. -/
def Performance.update : Performance W → Table Discourse.Role W → Table Discourse.Role W
  | ⟨.utterance D rising, _⟩ => utter D rising
  | _ => id

/-- A performance is an asking when in every context it raises an issue without committing its
speaker to anything that resolves it. -/
def Performance.Asking (u : Performance W) : Prop :=
  ∀ K : Table Discourse.Role W, ∃ i, (u.update K).stack = i :: K.stack ∧
    ∀ q ∈ (u.update K).discourseCommitments .speaker, q ∈ i → q ∈ K.discourseCommitments .speaker

/-- A performance is an assertion when in every context it raises an issue with a single
alternative and commits its speaker to that alternative. -/
def Performance.Assertion (u : Performance W) : Prop :=
  ∀ K : Table Discourse.Role W, ∃ q, (u.update K).stack = ofSet q :: K.stack ∧
    q ∈ (u.update K).discourseCommitments .speaker

namespace Performance

variable {D : Question W} {rising : Bool} {v : Volume}

private theorem stack_ne_of_update_eq_id {u : Performance W} (h : u.update = id) {i : Question W} :
    (u.update Table.empty).stack ≠ [i] := by
  rw [h]
  exact (List.cons_ne_nil i []).symm

theorem asking_utterance_iff :
    (⟨.utterance D rising, v⟩ : Performance W).Asking ↔ rising = true ∨ D.IsInquisitive := by
  cases rising with
  | true =>
    exact iff_of_true (fun _ ↦ ⟨D, rfl, fun q hq _ ↦ by simpa [update, utter] using hq⟩) (.inl rfl)
  | false =>
    refine ⟨fun h ↦ .inr fun hD ↦ ?_, fun h K ↦ ⟨D, rfl, fun q hq hqD ↦ ?_⟩⟩
    · obtain ⟨i, hi, hq⟩ := h Table.empty
      simp only [update, utter, Table.stack_push, Table.stack_commit, Table.stack_empty,
        List.cons.injEq, and_true] at hi
      subst hi
      simpa using hq _ (by simp [update, utter]) hD
    · simp only [update, utter, Table.discourseCommitments_push,
        Table.discourseCommitments_commit_self, Set.mem_insert_iff] at hq
      refine hq.resolve_left ?_
      rintro rfl
      exact (h.resolve_left Bool.false_ne_true) hqD

theorem not_asking_none : ¬ (⟨.none, v⟩ : Performance W).Asking := fun h ↦
  let ⟨_, hi, _⟩ := h Table.empty
  stack_ne_of_update_eq_id rfl hi

theorem not_asking_inarticulate : ¬ (⟨.inarticulate, v⟩ : Performance W).Asking := fun h ↦
  let ⟨_, hi, _⟩ := h Table.empty
  stack_ne_of_update_eq_id rfl hi

theorem assertion_utterance_iff :
    (⟨.utterance D rising, v⟩ : Performance W).Assertion ↔
      rising = false ∧ ¬ D.IsInquisitive := by
  cases rising with
  | true =>
    refine iff_of_false (fun h ↦ ?_) (by simp)
    obtain ⟨_, -, hq⟩ := h Table.empty
    simp [update, utter] at hq
  | false =>
    rw [← info_mem_iff_not_isInquisitive, info_mem_iff_eq_ofSet_info]
    refine ⟨fun h ↦ ⟨rfl, ?_⟩, fun ⟨_, h⟩ K ↦ ⟨D.info, by rw [← h]; rfl, by simp [update, utter]⟩⟩
    obtain ⟨q, hs, hq⟩ := h Table.empty
    simp only [update, utter, Table.stack_push, Table.stack_commit, Table.stack_empty,
      List.cons.injEq, and_true, Table.discourseCommitments_push,
      Table.discourseCommitments_commit_self, Table.discourseCommitments_empty,
      Set.mem_insert_iff, Set.mem_empty_iff_false, or_false] at hs hq
    exact hq ▸ hs

theorem not_assertion_none : ¬ (⟨.none, v⟩ : Performance W).Assertion := fun h ↦
  let ⟨_, hi, _⟩ := h Table.empty
  stack_ne_of_update_eq_id rfl hi

theorem not_assertion_inarticulate : ¬ (⟨.inarticulate, v⟩ : Performance W).Assertion := fun h ↦
  let ⟨_, hi, _⟩ := h Table.empty
  stack_ne_of_update_eq_id rfl hi

theorem not_asking_of_assertion {u : Performance W} (h : u.Assertion) : ¬ u.Asking := by
  obtain ⟨⟨⟩ | ⟨⟩ | ⟨D, rising⟩, v⟩ := u
  · exact (not_assertion_none h).elim
  · exact (not_assertion_inarticulate h).elim
  · obtain ⟨rfl, hD⟩ := assertion_utterance_iff.1 h
    simpa [asking_utterance_iff] using hD

open Classical in
noncomputable instance : (u : Performance W) → Decidable u.Asking
  | ⟨.utterance _ _, _⟩ => decidable_of_iff _ asking_utterance_iff.symm
  | ⟨.none, _⟩ => isFalse not_asking_none
  | ⟨.inarticulate, _⟩ => isFalse not_asking_inarticulate

open Classical in
noncomputable instance : (u : Performance W) → Decidable u.Assertion
  | ⟨.utterance _ _, _⟩ => decidable_of_iff _ assertion_utterance_iff.symm
  | ⟨.none, _⟩ => isFalse not_assertion_none
  | ⟨.inarticulate, _⟩ => isFalse not_assertion_inarticulate

end Performance

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

/-- `v.property` is what the meaning postulate of `v` requires of every performance reenacting one
of its events: linguistic material for *say*, an assertion for *assert* and *claim*, an asking for
*ask* and *wonder*, and loud or whispered linguistic material for the manner-of-speech verbs. -/
def Verb.property : Verb → Performance W → Prop
  | .say => fun u ↦ u.material.Linguistic
  | .assert | .claim => Performance.Assertion
  | .ask | .wonder => Performance.Asking
  | .yell | .shout => fun u ↦ u.material.Linguistic ∧ u.volume = .loud
  | .whisper => fun u ↦ u.material.Linguistic ∧ u.volume = .whispered

noncomputable instance (v : Verb) (u : Performance W) : Decidable (v.property u) := by
  cases v <;> simp only [Verb.property] <;> infer_instance

/-- Whatever a rising declarative is taken to denote, a proposition or a question, its quotation is
consistent under *ask* and contradictory under *assert*. -/
theorem report_rising_ask_assert [Nonempty E] (D : Question W) (v : Volume) :
    (∃ R : SetRel E (Performance W), ∃ e,
        report (□[R] Verb.ask.property) R ⟨.utterance D true, v⟩ e) ∧
      ∀ (R : SetRel E (Performance W)) e,
        ¬ report (□[R] Verb.assert.property) R ⟨.utterance D true, v⟩ e :=
  ⟨(exists_report_iff _ _).2 (Performance.asking_utterance_iff.2 (.inl rfl)),
    fun _ ↦ not_report le_rfl fun h ↦ by simpa using Performance.assertion_utterance_iff.1 h⟩

/-- Read right to left, the content postulate for *ask* (80) as printed makes every event an
asking once anything is a question, so under (86) the quotation of a falling declarative under
*say*, the paper's (60), is contradictory. -/
theorem not_report_say_of_printed {content : SetRel E X} {Dq : Set X}
    {R : SetRel E (Performance W)}
    (h80 : ∀ e x, (□[R] Verb.ask.property e ∧ e ~[content] x) ↔ x ∈ Dq) (hDq : Dq.Nonempty)
    (p : Set W) (v : Volume) (e : E) :
    ¬ report (□[R] Verb.say.property) R ⟨.utterance (ofSet p) false, v⟩ e := fun ⟨_, hu⟩ ↦
  ((h80 e _).2 hDq.some_mem).1 _ hu |> Performance.asking_utterance_iff.1 |>.elim
    Bool.false_ne_true (not_isInquisitive_ofSet p)

/-! ### The paper's judgments -/

def verbs : List (String × Verb) :=
  [("say", .say), ("assert", .assert), ("claim", .claim), ("ask", .ask), ("wonder", .wonder),
    ("yell", .yell), ("shout", .shout), ("whisper", .whisper)]

def volumes : List (String × Volume) :=
  [("neutral", .neutral), ("loud", .loud), ("whispered", .whispered)]

/-- `moods` gives the denotation of a quoted sentence of each mood on its radical: a declarative
denotes the radical, an interrogative the polar question on it. -/
def moods : List (String × (Set W → Question W)) :=
  [("declarative", ofSet), ("interrogative", polar)]

/-- `performance? x` is the quoted performance of the row `x`, its sentence radical a fixed
contingent proposition. -/
def performance? (x : Datum) : Option (Performance Bool) := do
  let volume ← x.parse? "volume" volumes
  let material ← match x.feature? "material" with
    | some "none" => some .none
    | some "inarticulate" => some .inarticulate
    | some "sentence" => do
      let mood ← x.parse? "mood" moods
      let rising ← x.parse? "tune" [("rising", true), ("falling", false)]
      pure (.utterance (mood {true}) rising)
    | _ => none
  pure ⟨material, volume⟩

/-- `datum x` reads the verb of speech and the quoted performance off the row `x`. -/
def datum (x : Datum) : Option (Verb × Performance Bool) := do
  pure (← x.parse? "verb" verbs, ← performance? x)

/-- `data` lists the paper's quotative reports. -/
def data : List (Datum × Verb × Performance Bool) :=
  Examples.all.filterMap fun x ↦ (datum x).map (x, ·)

/-- Each of the paper's quotative reports is judged acceptable exactly when it is consistent under
its verb's meaning postulate. -/
theorem judgments : ∀ d ∈ data, d.1.judgment = .acceptable ↔
    ∃ R : SetRel Unit (Performance Bool), ∃ e, report (□[R] d.2.1.property) R d.2.2 e := by
  simp only [exists_report_iff]
  decide +kernel

end Rudin2025b
