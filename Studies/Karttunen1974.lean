module

public import Linglib.Semantics.Tense.Before
public import Linglib.Logic.Trivalent.Proposition
public import Linglib.Semantics.PolarityItem.Polarity
public import Linglib.Languages.English.TemporalConnectives
public import Linglib.Languages.English.PolarityItems
public import Linglib.Languages.Finnish.TemporalConnectives
public import Linglib.Languages.Finnish.PolarityItems
public import Linglib.Languages.German.TemporalConnectives
public import Linglib.Languages.German.PolarityItems
public import Linglib.Data.Examples.Karttunen1974

/-!
# Karttunen (1974): Until

English *until* has two uses. Durative *until* modifies a durative clause and gives the least its
interval lasts: *A until T* holds when a run time of `A` begins before a time of `T` and reaches
it, whether or not it goes on. Punctual *until* is a negative polarity item with the logical form
of *before*. The sentence *A not until T* asserts $\neg (A \text{ before } T)$ and presupposes
$A \text{ before } T \lor A \text{ when } T$: the event comes in a stretch of time of which `T` is
the last part.

We define the sentence as a trivalent proposition, undefined where its presupposition fails. It
is true exactly where `A` is not before `T` and holds at a time of `T`, the disjunctive syllogism
of what it asserts and what it presupposes, and false exactly where `A` is before `T`. German
*erst* and Finnish *vasta* assert *A when T* with the same presupposition, and of an event that
occupies one moment the two sentences are the same proposition, though they assert different
things. On the one-*until* analysis, where negation is a durative predicate, *A not until T* is
durative *until* of the negated clause, and that holds of an event that never happens.

A sentence of the paper with a time expression is generated when the expression finds a reading:
the durative one over a durative clause, the punctual one where the clause's polarity admits the
expression's polarity item, or *before*. This gives the stars of the paper's sentences but for
three acceptable ones, *as long as* and *for* over a negated nondurative clause and German *bis*
with a clause. The one-*until* analysis, on which negation makes a clause durative, generates
those and eight starred sentences.

## Implementation notes

* A clause denotes its run times and `T` the run times of the *until*-phrase, the moment it names
  or the period that begins there, whose length the context sets. The paper leaves *before* and
  *when* schematic: *before* is `Tense.beforeEver`, the universal *before* of [anscombe-1964], a
  time of `A` before every time of `T`, and *when* is a time common to the two.
* A sentence with a presupposition is `Trivalent.condEvent`, what it asserts on what it
  presupposes. The paper's presupposition is pragmatic, a condition on the contexts that admit the
  sentence; a context admits a trivalent proposition when it entails where the proposition is
  defined (`Semantics/Presupposition/Context.lean`).
* The class of a clause, durative or not, and the negation, modifier and complement of a row are
  columns of the data file. Which expressions are durative is read off the relation of the
  language file's connective where it has one, and listed for *to*, *how long* and *for*. Finnish
  *ennen kuin* is the language's *before*, so its punctual use under negation is the logical form
  itself.
* A starred sentence is one the grammar does not generate. The `?` of *Nancy didn't get married
  until she died* is the clash of the sentence's truth, which needs a marriage at her death, with
  what is known of the dead, and is not a star.
* The rows with *at the earliest* and *at the latest*, whose pattern the paper leaves open, and
  the reduced and measure-phrase rows of the footnote on *before*, which do not turn on the class
  of the clause, are recorded and not read.

## TODO

* *As long as* and *for* over a negated nondurative clause, (6b) and (6c), are acceptable and not
  generated. The paper suggests a second, punctual *for*, and the English file has no such item.
* German *bis* with a clause after a negated nondurative clause is acceptable and not generated;
  the paper calls it an incipient punctual use.
* The rows carry no models, so the inferences the paper draws from its sentences, to *A when T*
  and from the denial to *A before T*, are theorems about `notUntil` and not checks on rows.

## References

* [karttunen-1974]
* [anscombe-1964]
-/

@[expose] public section

namespace Karttunen1974

open Tense Trivalent Temporal

variable {T : Type*} [LinearOrder T]

/-! ### Durative *until* -/

section Durative

variable {A A' B : NonemptyInterval T → Prop}

/-- Durative *A until T* holds when a run time of `A` begins before a time of `T` and reaches
it. -/
def until_ (A B : NonemptyInterval T → Prop) : Prop :=
  ∃ J, A J ∧ ∃ t ∈ timeTrace B, J.fst < t ∧ t ≤ J.snd

theorem until_.mono (h : until_ A B) (hA : A ≤ A') : until_ A' B :=
  let ⟨J, hJ, h⟩ := h; ⟨J, hA J hJ, h⟩

-- (12a)–(14a): the phrase gives the least the interval lasts, which may go on beyond it.
theorem until_subintervals_pure {i : NonemptyInterval T} {t : T} :
    until_ (· ≤ i) (· = NonemptyInterval.pure t) ↔ i.fst < t ∧ t ≤ i.snd := by
  refine ⟨?_, fun h ↦ ⟨i, le_rfl, t, mem_timeTrace_eq_pure.2 rfl, h⟩⟩
  rintro ⟨J, hJ, s, hs, hlt, hle⟩
  obtain rfl := mem_timeTrace_eq_pure.1 hs
  obtain ⟨h₁, h₂⟩ := NonemptyInterval.le_def.1 hJ
  exact ⟨h₁.trans_lt hlt, hle.trans h₂⟩

/-- The negated clause of the one-*until* analysis, on which negation is a durative predicate,
holds at the intervals in which `A` at no time holds. -/
def negated (A : NonemptyInterval T → Prop) : NonemptyInterval T → Prop :=
  fun i ↦ Disjoint (i : Set T) (timeTrace A)

theorem negated_iff {i : NonemptyInterval T} :
    negated A i ↔ Disjoint (i : Set T) (timeTrace A) := .rfl

-- The negated clause is closed under subintervals, as a durative clause is.
theorem antitone_negated (A : NonemptyInterval T → Prop) : Antitone (negated A) :=
  fun _ _ hji h ↦ h.mono_left (NonemptyInterval.coe_subset_coe.2 hji)

theorem negated_anti : Antitone (negated : (NonemptyInterval T → Prop) → _) :=
  fun _ _ hAB _ h ↦ h.mono_right (timeTrace_mono hAB)

@[simp] theorem negated_bot : negated (⊥ : NonemptyInterval T → Prop) = ⊤ := by
  ext; simp [negated]

/-- The narrow-scope reading of *A not until T*, (3a), durative *until* of the negated clause,
holds of an event that never happens. -/
theorem until_negated_bot {s t : T} (hst : s < t) (ht : t ∈ timeTrace B) :
    until_ (negated ⊥) B :=
  ⟨⟨(s, t), hst.le⟩, by simp, t, ht, hst, le_rfl⟩

end Durative

/-! ### Punctual *until* -/

section Punctual

variable {A B : NonemptyInterval T → Prop}

/-- *A when T* holds when `A` holds at a time of `T`. -/
def when_ (A B : NonemptyInterval T → Prop) : Prop := ∃ t, t ∈ timeTrace A ∧ t ∈ timeTrace B

/-- (34): the presupposition of lateness, *A before T or A when T*. -/
def presupposition (A B : NonemptyInterval T → Prop) : Prop := beforeEver A B ∨ when_ A B

theorem when_iff : when_ A B ↔ (timeTrace A ∩ timeTrace B).Nonempty := .rfl

-- An event that occupies one moment, a time of `T`, is not before `T`.
theorem not_beforeEver_of_when (hA : (timeTrace A).Subsingleton) (h : when_ A B) :
    ¬ beforeEver A B := fun ⟨_, hs, hlt⟩ ↦
  let ⟨t, htA, htB⟩ := h
  lt_irrefl t (hA hs htA ▸ hlt t htB)

variable {W : Type*} (A B : W → NonemptyInterval T → Prop)

open scoped Classical in
/-- (36): punctual *A not until T* asserts (33), *not (A before T)*, and presupposes (34). -/
noncomputable def notUntil : W → Trivalent :=
  condEvent (fun w ↦ presupposition (A w) (B w)) fun w ↦ ¬ beforeEver (A w) (B w)

open scoped Classical in
/-- German *erst* and Finnish *vasta* 'only then' assert *A when T* and presuppose (34). -/
noncomputable def onlyThen : W → Trivalent :=
  condEvent (fun w ↦ presupposition (A w) (B w)) fun w ↦ when_ (A w) (B w)

variable {A B} {w : W}

/-- By disjunctive syllogism, (36), *A not until T* is true exactly where `A` is not before `T`
and holds at a time of `T`. -/
theorem notUntil_eq_true_iff :
    notUntil A B w = .true ↔ ¬ beforeEver (A w) (B w) ∧ when_ (A w) (B w) := by
  simp only [notUntil, condEvent_eq_true_iff, presupposition]
  tauto

-- (30)–(31): the sentence is false exactly where `A` is before `T`.
theorem notUntil_eq_false_iff : notUntil A B w = .false ↔ beforeEver (A w) (B w) := by
  simp only [notUntil, condEvent_eq_false_iff, presupposition]
  tauto

theorem notUntil_eq_undefined_iff :
    notUntil A B w = .undefined ↔ ¬ beforeEver (A w) (B w) ∧ ¬ when_ (A w) (B w) := by
  simp [notUntil, presupposition]

open scoped Classical Bilattice in
-- (33): where it is defined, the sentence has the truth value of *A not before T*.
theorem notUntil_kLE : notUntil A B w ≤ₖ ofProp (¬ beforeEver (A w) (B w)) := condEvent_kLE

-- (23), (25a): the sentence is true only of an event that happens, unlike *A not before T*.
theorem exists_of_notUntil_eq_true (h : notUntil A B w = .true) : ∃ i, A w i :=
  let ⟨_, _, ⟨i, hi, _⟩, _⟩ := notUntil_eq_true_iff.1 h
  ⟨i, hi⟩

theorem onlyThen_eq_true_iff : onlyThen A B w = .true ↔ when_ (A w) (B w) := by
  simp only [onlyThen, condEvent_eq_true_iff, presupposition]
  tauto

-- (38b): of an event that occupies one moment, the sentence is false exactly where `A` is before
-- `T`.
theorem onlyThen_eq_false_iff (hA : (timeTrace (A w)).Subsingleton) :
    onlyThen A B w = .false ↔ beforeEver (A w) (B w) := by
  simp only [onlyThen, condEvent_eq_false_iff, presupposition]
  exact ⟨fun ⟨h, hn⟩ ↦ h.resolve_right hn, fun h ↦ ⟨.inl h, fun hw ↦
    not_beforeEver_of_when hA hw h⟩⟩

/-- Of an event that occupies one moment, *A not until T* and the sentence of *erst* and *vasta*
are the same proposition, as (39a) and (39b) are synonymous. -/
theorem notUntil_eq_onlyThen (hA : ∀ w, (timeTrace (A w)).Subsingleton) :
    notUntil A B = onlyThen A B :=
  funext fun w ↦ eq_of_eq_undefined_iff_of_eq_true_iff (by simp [notUntil, onlyThen]) <| by
    rw [notUntil_eq_true_iff, onlyThen_eq_true_iff]
    exact ⟨And.right, fun h ↦ ⟨not_beforeEver_of_when (hA w) h, h⟩⟩

-- An event that recurs, before `T` and at `T`, separates the two sentences.
theorem exists_notUntil_eq_false_onlyThen_eq_true :
    ∃ A B : Unit → NonemptyInterval ℤ → Prop, notUntil A B () = .false ∧ onlyThen A B () = .true :=
  ⟨fun _ ↦ (· = .pure 0) ⊔ (· = .pure 1), fun _ ↦ (· = .pure 1),
    notUntil_eq_false_iff.2 ⟨0, by simp, by simp⟩, onlyThen_eq_true_iff.2 ⟨1, by simp, by simp⟩⟩

end Punctual

/-! ### The paper's sentences -/

namespace Examples

/-- The connective of a time expression, where the language file enters it as one. -/
def Adverbial.connective : Adverbial → Option Tense.Connective
  | .until => some English.TemporalConnectives.until_
  | .before => some English.TemporalConnectives.before
  | .whilePhrase => some English.TemporalConnectives.while_
  | .asLongAs => some English.TemporalConnectives.asLongAs
  | .bis => some German.TemporalConnectives.bis
  | .ennenKuin => some Finnish.TemporalConnectives.ennenKuin
  | .to | .howLong | .forPhrase | .erst | .vasta => none

/-- The polarity item a time expression is or doubles as. -/
def Adverbial.polarityItem : Adverbial → Option PolarityItem.Class
  | .until => some (.npi .antiAdditive)
  | .erst | .vasta => some (.ppi .antimorphic)
  | _ => none

/-- A time expression is durative when it measures the interval of a durative clause: a
connective of the relations *until*, *while* and *as long as*, and *to*, *how long* and *for*. -/
def Adverbial.Durative (a : Adverbial) : Prop :=
  (∃ c ∈ a.connective, c.relation = .until_ ∨ c.relation = .while_ ∨ c.relation = .asLongAs) ∨
    a = .to ∨ a = .howLong ∨ a = .forPhrase

instance : DecidablePred Adverbial.Durative := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- A time expression is a *before* when its connective relates the clauses by precedence. -/
def Adverbial.Before (a : Adverbial) : Prop := ∃ c ∈ a.connective, c.relation = .before

instance : DecidablePred Adverbial.Before := fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The polarity of the clause a time expression stands in, negative under a negation of the
clause or of a superordinate *think*. -/
def Example.polarity (x : Example) : Polarity :=
  if x.negation.isSome then .negative else .positive

/-- A sentence is generated when its time expression finds a reading and the clause of an
*until*-phrase is not exclusively durative. The durative reading needs a durative clause, the
punctual reading a polarity item that the polarity of the clause admits, with no qualification of
an interval's end, and a *before* needs neither. -/
def Example.Generated (x : Example) : Prop :=
  x.complement ≠ some .durative ∧ ∃ a ∈ x.adverbial,
    (a.Durative ∧ x.host = some .durative) ∨
      (∃ i ∈ a.polarityItem, x.polarity.Admits i ∧ x.modifier = none) ∨ a.Before

instance : DecidablePred Example.Generated := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- On the one-*until* analysis there is one durative reading, which a durative clause or a
negated one supplies. -/
def Example.GeneratedOneUntil (x : Example) : Prop :=
  x.complement ≠ some .durative ∧ ∃ a ∈ x.adverbial,
    (a.Durative ∧ (x.host = some .durative ∨ x.polarity = .negative)) ∨ a.Before

instance : DecidablePred Example.GeneratedOneUntil :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- A row is read when the paper gives the class of its clause and its phrase is not qualified by
*at the earliest* or *at the latest*. -/
def Example.Read (x : Example) : Prop :=
  x.host.isSome ∧ x.modifier ≠ some .atTheEarliest ∧ x.modifier ≠ some .atTheLatest

instance : DecidablePred Example.Read := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

end Examples

open Examples

/-- The two *until*s give the stars of the paper's sentences: but for (6b), (6c) and the clause
of German *bis*, a sentence is starred exactly when it is not generated. -/
theorem ungrammatical_iff_not_generated (x : Example) (hx : x.Read)
    (he : x ∉ [Example.ex_6b, .ex_6c, .fn8_clause]) :
    x.datum.judgment = .ungrammatical ↔ ¬ x.Generated := by
  revert hx he; cases x <;> decide

-- (6b), (6c) and the clause of German *bis* are acceptable, and only the one-*until* analysis
-- generates them.
theorem acceptable_not_generated (x : Example) (he : x ∈ [Example.ex_6b, .ex_6c, .fn8_clause]) :
    x.datum.judgment = .acceptable ∧ ¬ x.Generated ∧ x.GeneratedOneUntil := by
  revert he; cases x <;> decide

theorem read_count : (Example.all.filter Example.Read).length = 61 := by decide

/-- The one-*until* analysis generates eight starred sentences: the negated nondurative clauses
with *to*, *how long* and *while*, (8c), (9b) and (10c), with a qualified *until*-phrase, (12b),
(13b) and (14b), and with German *bis*. -/
theorem ungrammatical_and_generatedOneUntil_iff (x : Example) (hx : x.Read) :
    x.datum.judgment = .ungrammatical ∧ x.GeneratedOneUntil ↔
      x ∈ [Example.ex_8c, .ex_9b, .ex_10c, .ex_12b, .ex_13b_longer, .ex_13b_more, .ex_14b,
        .fn8_np] := by
  revert hx; cases x <;> decide

end Karttunen1974
