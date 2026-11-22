module

public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.Aspect.Viewpoint.Basic
public import Linglib.Semantics.Focus.Particles
public import Linglib.Semantics.Tense.Defs
public import Linglib.Data.Examples.Eckardt2006
public import Studies.Krifka1995
public import Linglib.Data.Statistics.Eckardt2006

/-!
# Eckardt (2006): Meaning Change in Grammaticalization

In *semantic reanalysis* a sentence keeps the information it conveys while that information is
composed in a new way, and what was an inference from the literal content becomes the literal
content. This file follows the emergence of the English *going to* future.

Movement *go* with an infinitive denotes the goings of `x` that prepare an event of the embedded
predicate: `goTo go prepare P x w e` holds when `go x w e` and `prepare e e'` and `P x w e'` for
some `e'`. Like any event predicate it takes a viewpoint, and in the progressive the reference
time lies within the going. The reanalysed *be going to* is an interval property: `beGoingTo imm P
x w` holds of a reference time `t` when `t` precedes an event `e` of `P x w` with `imm t e`, where
`imm` says which events count as imminent at a time.

When a preparation precedes what it prepares, and a going in progress makes what it prepares
imminent, the progressive of the old entry entails the new one (`unbounded_goTo_le_beGoingTo`): the
inference that the planned event is imminent is a consequence of where the reference time lies. The
entailment holds under the present and under every tense (`beGoingTo_pure_of_unbounded_goTo`,
`diamond_goTo_le`), and in each world accessible along the modal imperfective
(`imperfective_goTo_le`). The new entry is a restriction of the prospective viewpoint
(`beGoingTo_le_prospective`) and conveys no movement (`unbounded_goTo_eq_bot`).

The old entry holds of nothing when no going prepares an event of the embedded predicate, under
every viewpoint (`diamond_runTimes_goTo_eq_bot`). A simple form has only the old entry, so it is
acceptable only where the embedded clause allows the movement interpretation, and German *gehen*,
which has no future entry, behaves in every form as the English simple forms do (`licensed_iff`).

For the French negation particles a lexical entry is a `FocusEntry`: an ordinary value, focus
alternatives of the same type, and possibly the requirement of emphatic focus. An emphatic
assertion presupposes that the sentence is less likely than each of its focus alternatives, so an
entry is licensed in a sentence frame `S` when `evenPresup μ (S value) (S '' alternatives)` holds
if it is emphatic (`FocusEntry.Licensed`). Where an alternative entails the sentence, an emphatic
entry is not licensed under a monotone operator (`FocusEntry.not_licensed_of_monotone`), and under
an antitone one it is licensed exactly when no alternative is as likely as the sentence
(`FocusEntry.licensed_iff_of_antitone`). An entry that does not require emphasis is licensed
everywhere (`FocusEntry.licensed_of_not_emphatic`).

*Mie* maps an event description to its smallest events, `mie V = {e | Minimal (· ∈ V) e}`, and
its alternatives are other degree adverbs. Where whatever is done to some degree is done to a
minimal degree, as in a well-founded part order (`mie_nonempty`), a clause with a restrictive
degree adverb entails the clause with *mie* (`clause_subset_clause_mie`), which makes *mie* a
polarity item. *Pas* gives the subminimal parts of the events of a description
(`IsSubminimal`). There is a subminimal part exactly when there is an event of the description
(`IsSubminimal.nonempty_iff`), so a clause with *pas* is true where the clause without it is
(`clause_eq_of_isSubminimal`).

## Implementation notes

* The progressive is the extensional `Aspect.unbounded`, the reference time within the run time of
  the event, as in the source. `imperfective_goTo_le` states the entailment for the modal
  imperfective, where an event in progress need not be completed: there the planned event follows
  the reference time in every accessible world, and in the world of evaluation only if it is
  accessible.
* The new entry has strict precedence, the reference time ending before the event starts, where the
  prospective viewpoint allows the two to meet.
* `goTo` is an event predicate and `beGoingTo` an interval property. That the progressive is no
  longer a part of the reanalysed sentence is this difference of type: no viewpoint operator applies
  to the new entry.
* `imm` is the one parameter of the new entry that the context supplies and the old entry lacks.
* An entry with a sentence frame is a BFA structure of [krifka-1995a] (`FocusEntry.bfa`), and
  licensing is the first of the two conditions of his emphatic assertion, taken in the common
  ground of all worlds (`FocusEntry.licensed_of_emphAssertable`). His scalar assertion, which he
  uses for the weak items, plays no part here: every item is licensed through emphatic assertion.
* The focus semantic value of a sentence is the image of the entry's alternatives under the
  sentence frame, the pointwise composition of focus semantics. The likelihood `μ` is any monotone
  map into a partial order, a ranking that respects entailment.
* `IsSubminimal` has the three conditions of (5.90) as printed, with strict parthood in each.
* That a negated clause with *pas* has the truth conditions of plain negation is a consequence of
  (5.90) drawn here, `clause_eq_of_isSubminimal`. The restriction of the later particles to
  negation is not derived: an entry without the emphatic requirement is licensed in every frame.

## TODO

* The manner adverbs that the new entry excludes, *carefully going to travel*, are not treated.
* The contexts of the positive uses (`positiveUses`) are not yet mapped to the licensing contexts
  of `Semantics/PolarityItem`, and the entries of *goutte*, *personne* and temporal *mie* are not
  given.
* The scalar implicature that confines *pas* to non-veridical contexts is stated only through its
  premise, `IsSubminimal.nonempty_iff`.
* The reanalyses of *selbst* and *lauter* are not treated.

## References

* [eckardt-2006]
* [krifka-1995a]
-/

@[expose] public section

namespace Eckardt2006

open Aspect ModalLogic PointAlgebra
open scoped Denotes SetRel
open Event (τ)
open Examples (Example Verb Form Movement)

variable {W X E T : Type*} [LinearOrder T] [TemporalTrace E T]
  {go : X → W → E → Prop} {prepare : E → E → Prop} {P : X → W → E → Prop}
  {imm imm' : NonemptyInterval T → E → Prop} {x : X} {w : W} {t : NonemptyInterval T}

/-! ### The two entries -/

/-- (4.50a): Movement *go* with an infinitive holds of a going by `x` that prepares an event in
which `x` does what the embedded clause describes. -/
def goTo (go : X → W → E → Prop) (prepare : E → E → Prop) (P : X → W → E → Prop) (x : X) :
    W → E → Prop :=
  fun w e ↦ go x w e ∧ ∃ e', prepare e e' ∧ P x w e'

/-- (4.58): The reanalysed *be going to* holds of a reference time that precedes an imminent event
of the embedded predicate. -/
def beGoingTo (imm : NonemptyInterval T → E → Prop) (P : X → W → E → Prop) (x : X) (w : W) :
    NonemptyInterval T → Prop :=
  fun t ↦ ∃ e, t.Precedes (τ e) ∧ imm t e ∧ P x w e

theorem beGoingTo_iff :
    beGoingTo imm P x w t ↔ ∃ e, t.Precedes (τ e) ∧ imm t e ∧ P x w e := Iff.rfl

theorem beGoingTo_mono (h : ∀ t e, imm t e → imm' t e) :
    beGoingTo imm P x w ≤ beGoingTo imm' P x w :=
  fun _ ⟨e, ht, hi, hP⟩ ↦ ⟨e, ht, h _ _ hi, hP⟩

theorem beGoingTo_le_prospective :
    beGoingTo imm P x w ≤ ViewpointType.prospective.denote (P x w) :=
  fun _ ⟨e, ht, _, hP⟩ ↦ denote_prospective_iff.2 ⟨e, le_of_lt ht, hP⟩

/-! ### From the inference to the literal content -/

section Inference

variable (hprep : ∀ e e', prepare e e' → Event.Precedes e e')
  (himm : ∀ w t e e', go x w e → prepare e e' → t ≤ τ e → imm t e')

include hprep himm

/-- (4.54): Where preparations precede what they prepare and a going in progress makes what it
prepares imminent, the progressive of movement *go* entails the reanalysed *be going to*. -/
theorem unbounded_goTo_le_beGoingTo :
    unbounded (goTo go prepare P x w) ≤ beGoingTo imm P x w := by
  intro t ht
  obtain ⟨e, hte, hgo, e', hpr, hP⟩ := unbounded_iff.1 ht
  exact ⟨e', lt_of_le_of_lt (NonemptyInterval.le_def.1 hte).2 (hprep e e' hpr),
    himm w t e e' hgo hpr hte, hP⟩

-- (4.50f) and (4.56): the entailment under the present tense.
theorem beGoingTo_pure_of_unbounded_goTo {a : T}
    (h : unbounded (goTo go prepare P x w) (.pure a)) : beGoingTo imm P x w (.pure a) :=
  unbounded_goTo_le_beGoingTo hprep himm _ h

-- (4.51) and (4.60): the entailment under every tense.
theorem diamond_goTo_le (tn : Tense) :
    ◇[toSetRel ⟦tn⟧] (fun r ↦ unbounded (goTo go prepare P x w) (.pure r)) ≤
      ◇[toSetRel ⟦tn⟧] (fun r ↦ beGoingTo imm P x w (.pure r)) :=
  diamond_mono _ fun _ hr ↦ beGoingTo_pure_of_unbounded_goTo hprep himm hr

-- The entailment in each world accessible along the modal imperfective.
theorem imperfective_goTo_le {acc : NonemptyInterval T → SetRel W W} :
    imperfective acc (goTo go prepare P x) w ≤
      fun t ↦ □[acc t] (fun v ↦ beGoingTo imm P x v t) w :=
  fun _ ht v hv ↦ unbounded_goTo_le_beGoingTo hprep himm _ (ht v hv)

end Inference

-- The reference time of a progressive is not before its own event.
theorem not_precedes_of_le {s : NonemptyInterval T} (h : t ≤ s) : ¬ t.Precedes s :=
  fun hp ↦ absurd (lt_of_le_of_lt ((NonemptyInterval.le_def.1 h).1.trans t.fst_le_snd) hp)
    (lt_irrefl _)

/-! ### What the new entry no longer conveys -/

theorem diamond_runTimes_goTo_eq_bot (R : SetRel (NonemptyInterval T) (NonemptyInterval T))
    (h : ∀ e e', go x w e → prepare e e' → ¬ P x w e') :
    ◇[R] (Event.runTimes (goTo go prepare P x w)) = ⊥ :=
  eq_bot_iff.2 fun _ ht ↦
    let ⟨e, _, hgo, e', hpr, hP⟩ := Event.diamond_runTimes_iff.1 ht; h e e' hgo hpr hP

theorem unbounded_goTo_eq_bot (h : ∀ e, ¬ go x w e) :
    unbounded (goTo go prepare P x w) = ⊥ :=
  diamond_runTimes_goTo_eq_bot _ fun e _ hgo _ ↦ (h e hgo).elim

-- A time at which something is going to happen though nothing moves.
theorem beGoingTo_pure :
    beGoingTo (E := NonemptyInterval ℕ) (fun _ _ ↦ True)
      (fun (_ _ : Unit) e ↦ e = .pure 1) () () (.pure 0) :=
  ⟨.pure 1, Nat.zero_lt_one, trivial, rfl⟩

/-! ### Simple forms and German *gehen* -/

/-- The two entries of a verb of movement with an infinitive. -/
inductive Entry where
  /-- The going prepares what the embedded clause describes. -/
  | movement
  /-- What the embedded clause describes is imminent. -/
  | future
  deriving DecidableEq, Fintype, Repr

/-- The entries a form of a verb has: every form has the movement entry, and only *be going to*
the future one. -/
def Entry.Available : Entry → Verb → Form → Prop
  | .movement, _, _ => True
  | .future, v, f => v = .go ∧ f = .goingTo

instance (n : Entry) (v : Verb) (f : Form) : Decidable (n.Available v f) := by
  cases n <;> unfold Entry.Available <;> infer_instance

/-- The embedded clauses an entry combines with: the movement entry needs a clause for which a
going can be a preparation. -/
def Entry.Admits : Entry → Movement → Prop
  | .movement, m => m = .possible
  | .future, _ => True

instance (n : Entry) (m : Movement) : Decidable (n.Admits m) := by
  cases n <;> unfold Entry.Admits <;> infer_instance

/-- A form with an embedded clause is licensed when one of its entries combines with the
clause. -/
def Licensed (v : Verb) (f : Form) (m : Movement) : Prop :=
  ∃ n : Entry, n.Available v f ∧ n.Admits m

instance (v : Verb) (f : Form) (m : Movement) : Decidable (Licensed v f m) :=
  inferInstanceAs (Decidable (∃ _, _))

/-- The examples are acceptable exactly where a form is licensed. -/
theorem licensed_iff (e : Example) :
    ∀ v ∈ e.verb, ∀ f ∈ e.form, ∀ m ∈ e.movement,
      (Licensed v f m ↔ e.datum.judgment = .acceptable) := by
  cases e <;> decide

/-! ### Emphatic assertion and polarity items -/

section Emphatic

open Focus

variable {D α : Type*} [PartialOrder α] {μ : Set W → α} {Q : Set W → Set W} {S : D → Set W}

/-- (5.88): A lexical entry has an ordinary value, focus alternatives of the same type, and may
have to be used in emphatic focus. -/
structure FocusEntry (D : Type*) where
  /-- The ordinary semantic value. -/
  value : D
  /-- The focus alternatives. -/
  alternatives : Set D
  /-- The entry must be used in emphatic focus. -/
  emphatic : Prop

namespace FocusEntry

variable {i : FocusEntry D} {a : D}

/-- (5.72): An entry is licensed in a sentence frame when, if it requires emphatic focus, the
sentence is less likely than each of its focus alternatives. -/
def Licensed (μ : Set W → α) (S : D → Set W) (i : FocusEntry D) : Prop :=
  i.emphatic → evenPresup μ (S i.value) (S '' i.alternatives)

/-- The BFA structure of [krifka-1995a] that an entry forms with a sentence frame as its
background. -/
def bfa (S : D → Set W) (i : FocusEntry D) : Krifka1995.BFA W D := ⟨S, i.value, i.alternatives⟩

-- An operator on the sentence applies to the background, as in Krifka's rule.
theorem bfa_comp (Q : Set W → Set W) (S : D → Set W) (i : FocusEntry D) :
    i.bfa (Q ∘ S) = (i.bfa S).map Q := rfl

-- (5.72) asks for the first condition of Krifka's emphatic assertion, in the common ground of all
-- worlds, and not for the second.
theorem licensed_of_emphAssertable
    (h : Krifka1995.BFA.EmphAssertable (fun p q ↦ μ p < μ q) (i.bfa S) Set.univ) :
    i.Licensed μ S := fun _ ↦ by
  rintro _ ⟨a, ha, rfl⟩
  simpa [Krifka1995.BFA.prop, bfa] using h.lt_of_mem a ha

-- The loss of emphasis: without the requirement an entry is licensed in every frame.
theorem licensed_of_not_emphatic (h : ¬ i.emphatic) : i.Licensed μ S := fun he ↦ absurd he h

-- (5.78)
theorem not_licensed_of_monotone (hμ : Monotone μ) (hQ : Monotone Q) (he : i.emphatic)
    (ha : a ∈ i.alternatives) (h : S a ⊆ S i.value) : ¬ i.Licensed μ (Q ∘ S) :=
  fun hl ↦ not_evenPresup_image hμ ha (hQ h) (hl he)

/-- (5.80): Under an antitone operator an emphatic entry whose alternatives all entail the
sentence is licensed exactly when no alternative is as likely as the sentence. -/
theorem licensed_iff_of_antitone (hμ : Monotone μ) (hQ : Antitone Q) (he : i.emphatic)
    (h : ∀ a ∈ i.alternatives, S a ⊆ S i.value) :
    i.Licensed μ (Q ∘ S) ↔ ∀ a ∈ i.alternatives, μ (Q (S i.value)) ≠ μ (Q (S a)) := by
  rw [Licensed, imp_iff_right he]
  exact evenPresup_image_iff_ne hμ fun a ha ↦ hQ (h a ha)

end FocusEntry

end Emphatic

/-! ### *Mie* and *pas* -/

section Minimizers

open Focus

variable {Ev α : Type*} [PartialOrder Ev] [PartialOrder α] {μ : Set W → α}
  {Q : Set W → Set W} {V : W → Set Ev} {U : Set Ev} {A : Set Ev → Set Ev}
  {alts : Set (Set Ev → Set Ev)}

/-- (5.88): *Mie* maps an event description to its smallest events. -/
def mie (U : Set Ev) : Set Ev := {e | Minimal (· ∈ U) e}

theorem mie_subset (U : Set Ev) : mie U ⊆ U := fun _ h ↦ h.prop

-- In a well-founded part order whatever is done to some degree is done to a minimal degree.
theorem mie_nonempty [WellFoundedLT Ev] (h : U.Nonempty) : (mie U).Nonempty :=
  exists_minimal_of_wellFoundedLT _ h

/-- The clause in which a degree adverb modifies an event description: some event of the modified
description takes place. -/
def clause (V : W → Set Ev) (A : Set Ev → Set Ev) : Set W := {w | (A (V w)).Nonempty}

/-- A clause with a restrictive degree adverb entails the clause with *mie*, where whatever is
done to some degree is done to a minimal degree. -/
theorem clause_subset_clause_mie (hA : ∀ U, A U ⊆ U)
    (hmin : ∀ w, (V w).Nonempty → (mie (V w)).Nonempty) : clause V A ⊆ clause V mie :=
  fun w hw ↦ hmin w (hw.mono (hA _))

/-- (5.88): The entry of *mie*, with other degree adverbs as its alternatives and the requirement
of emphatic focus. -/
def mieEntry (alts : Set (Set Ev → Set Ev)) : FocusEntry (Set Ev → Set Ev) := ⟨mie, alts, True⟩

-- (5.77): *mie* in a positive sentence.
theorem not_licensed_mieEntry (hμ : Monotone μ) (hQ : Monotone Q) (hA : A ∈ alts)
    (hAr : ∀ U, A U ⊆ U) (hmin : ∀ w, (V w).Nonempty → (mie (V w)).Nonempty) :
    ¬ (mieEntry alts).Licensed μ (Q ∘ clause V) :=
  FocusEntry.not_licensed_of_monotone hμ hQ trivial hA (clause_subset_clause_mie hAr hmin)

-- (5.79): *mie* under a downward-entailing operator.
theorem licensed_mieEntry_iff (hμ : Monotone μ) (hQ : Antitone Q)
    (hr : ∀ A ∈ alts, ∀ U, A U ⊆ U) (hmin : ∀ w, (V w).Nonempty → (mie (V w)).Nonempty) :
    (mieEntry alts).Licensed μ (Q ∘ clause V) ↔
      ∀ A ∈ alts, μ (Q (clause V mie)) ≠ μ (Q (clause V A)) :=
  FocusEntry.licensed_iff_of_antitone hμ hQ trivial fun A hA ↦
    clause_subset_clause_mie (hr A hA) hmin

/-- (5.90): The subminimal parts of the events of a description. Every event of the description
has one as a proper part, each is a proper part of an event of the description, and none has an
event of the description as a proper part. -/
structure IsSubminimal (pas U : Set Ev) : Prop where
  /-- (i): Every event of the description has a subminimal part. -/
  exists_lt_of_mem : ∀ e ∈ U, ∃ e' ∈ pas, e' < e
  /-- (ii): Every subminimal part is a proper part of an event of the description. -/
  exists_gt_of_mem : ∀ e' ∈ pas, ∃ e ∈ U, e' < e
  /-- (iii): No subminimal part has an event of the description as a proper part. -/
  not_lt_of_mem : ∀ e' ∈ pas, ¬ ∃ e ∈ U, e < e'

/-- There is a subminimal part exactly when there is an event of the description. -/
theorem IsSubminimal.nonempty_iff {pas : Set Ev} (h : IsSubminimal pas U) :
    pas.Nonempty ↔ U.Nonempty :=
  ⟨fun ⟨e', he'⟩ ↦ let ⟨e, he, _⟩ := h.exists_gt_of_mem e' he'; ⟨e, he⟩,
    fun ⟨e, he⟩ ↦ let ⟨e', he', _⟩ := h.exists_lt_of_mem e he; ⟨e', he'⟩⟩

-- A clause with *pas* is true where the clause without it is.
theorem clause_eq_of_isSubminimal {pas : Set Ev → Set Ev} (h : ∀ U, IsSubminimal (pas U) U) :
    clause V pas = clause V id :=
  Set.ext fun w ↦ (h (V w)).nonempty_iff

end Minimizers

/-! ### The positive uses of the particles -/

-- Table 4: *pas* has a positive sense only under negation and in rhetorical questions.
theorem pas_mem_positiveUses_iff (c : Context) :
    .pas ∈ (positiveUses c).particles ↔ c = .negation ∨ c = .rhetoricalQuestion := by
  cases c <;> decide

-- Table 4: every particle has a positive sense in a clause embedded under negation.
theorem mem_positiveUses_negation (p : Particle) : p ∈ (positiveUses .negation).particles := by
  cases p <;> decide

end Eckardt2006
