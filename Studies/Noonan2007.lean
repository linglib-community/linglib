module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.Examples.Noonan2007
public import Linglib.Fragments.English.Verbs.Inventory

/-!
# Noonan (2007): Complementation

Noonan's survey classifies complement clauses by their morphology (`Complement.Coding`) and
complement-taking predicates (ctps) by the semantic classes that select among the codings. This
file checks three of the chapter's generalizations against the English verb fragment and the
chapter's examples.

Equi-deletion, the deletion of a complement subject coreferential with a matrix argument, always
leaves a complement that is not sentence-like (§2.1). No complement of an English verb that a
participant controls is indicative or subjunctive (`not_isSLike_of_controlled`), and *hope* takes
a controlled infinitive beside an uncontrolled indicative (`hope_diatheses`).

Negative raising, the reading of a matrix negation in the complement, is confined to propositional
attitude, desiderative and modal predicates (§2.7). *Think*, *believe* and *want* allow it in
(214)–(216), and the commentative *regret* does not in (218) (`lowerNeg_iff`).

A complement has dependent time reference (dtr) when its time is fixed by the meaning of the ctp,
and independent time reference (itr) otherwise (§3.1.1). Each class's complements have one or the
other (§3.2), and the two go with reduced and indicative complements respectively (§3.1.2). No
English verb of a dtr class takes an s-like complement (`not_isSLike_of_dependent`), and every one
of an itr class whose complement the fragment codes takes an indicative
(`indicative_mem_codings_of_independent`). The desideratives fit neither, since *want* takes only
a reduced complement and *wish* an indicative (`want_wish_codings`), as the chapter's want-class
(dtr) and wish-class (itr) predict.

## Implementation notes

* A class classifies a use of a ctp rather than a verb, as *tell* is an utterance predicate with
  a *that*-clause and a manipulative one with an infinitive (§3.2). The fragment enters such uses
  as separate verbs (*remember* and *forget* with an infinitive are implicatives, with a
  *that*-clause veridical doxastics), so a verb's class is read off its entry. An entry is in a
  class when it records the property the chapter identifies the class by: commentatives are the
  emotive factives (§3.2.4), predicates of knowledge the veridical doxastics, which the chapter
  calls semifactives (§3.2.5), manipulatives have an affectee controlling the complement
  (§3.2.8), and achievement predicates are Karttunen's implicatives (§3.2.10). The fragment's
  implicative signature also covers the manipulatives *force* and *make*, so an implicative with
  an affectee is manipulative only. Nothing in an entry picks out pretence, modal, immediate
  perception, negative or conjunctive predicates.
* Equi is control by a matrix participant with the complement subject left null. An English
  controlled complement has a null subject, so control is equi in the English fragment.

## TODO

* Raising also leaves a complement that is not sentence-like (§2.2).
* Table 2.3 distributes realis and irrealis modality over complement roles, which neither the
  fragment nor the rows record.
* The fragment's *believe* lacks the infinitive of (260), *I believe Zeke to be an idiot*, which
  §3.1.2 discusses as an exception to the association of infinitives with dtr, and its *see*
  lacks the immediate-perception use (347), *I saw Floyd leave*, beside the knowledge use (346).

## References

* [noonan-2007]
-/

@[expose] public section

namespace Noonan2007

open English.Verbs (verbs hope think believe want regret wish)

/-! ### Equi-deletion -/

/-- Equi-deletion always results in a non-sentence-like complement ([noonan-2007] §2.1). No
complement of an English verb that a participant controls is s-like. -/
theorem not_isSLike_of_controlled : ∀ v ∈ verbs, ∀ d ∈ v.valency.diatheses,
    d.controller.isSome → ∀ c ∈ d.codings, ¬ c.IsSLike := by
  decide +kernel

/-- *hope* takes an indicative complement nobody controls and an infinitive its subject controls,
equi-deleted as in *Zeke wants to plant the corn* (106). -/
theorem hope_diatheses : hope.valency.diatheses.map (fun d ↦ (d.controller.isSome, d.codings)) =
    [(false, [.indicative]), (true, [.infinitive])] := by
  decide

/-! ### Classes of complement-taking predicates -/

/-- The fourteen classes of complement-taking predicate of [noonan-2007] §3.2, in its order. -/
inductive PredicateClass where
  /-- Predicates of a transfer of information initiated by an agent, such as *say*, *tell* and
  *report* (§3.2.1). -/
  | utterance
  /-- Predicates of a positive or negative attitude towards the truth of the complement, such as
  *believe*, *think*, *doubt* and *deny* (§3.2.2). -/
  | propositionalAttitude
  /-- Predicates whose complement describes a world other than the real one, such as *imagine*,
  *pretend* and *make believe* (§3.2.3). -/
  | pretence
  /-- The factives, predicates of an emotional reaction to or evaluation of a complement taken
  as background, such as *regret*, *be sorry* and *be sad* (§3.2.4). -/
  | commentative
  /-- The semifactives, predicates of the state or acquisition of knowledge, such as *know*,
  *discover*, *realize*, *find out* and *forget* (§3.2.5). -/
  | knowledge
  /-- Predicates of fear or concern that the complement will be or has been realized, such as
  *fear*, *worry* and *be afraid* (§3.2.6). -/
  | fearing
  /-- Predicates of a desire that the complement be realized, such as *want*, *wish*, *desire*
  and *hope* (§3.2.7). -/
  | desiderative
  /-- Predicates relating a cause, an affectee and a resulting situation in which the affectee
  takes part, such as *cause*, *force*, *make*, *persuade* and *let* (§3.2.8). -/
  | manipulative
  /-- Predicates of obligation, necessity and ability, such as *can*, *be able*, *ought* and
  *should* (§3.2.9). -/
  | modal
  /-- Karttunen's implicatives, predicates of the realization or not of the complement, such as
  *manage*, *dare*, *try*, *fail* and *forget to* (§3.2.10). -/
  | achievement
  /-- Predicates of the inception, continuation or termination of an act or state, such as
  *begin*, *continue* and *stop* (§3.2.11). -/
  | phasal
  /-- Predicates of direct sensory perception of the complement's event, such as *see*, *hear*,
  *watch* and *feel* (§3.2.12). -/
  | perception
  /-- Negation as a ctp, as Fijian *sega* and Shuswap *táʔ* express it (§3.2.13). -/
  | negative
  /-- Verbs translating *and* or *and then*, such as Lango *tε̂* (§3.2.14). -/
  | conjunctive
  deriving DecidableEq, Repr, Fintype

/-- A participant of some diathesis of the verb is its affectee, a direct object controlling the
complement. -/
def HasAffectee (v : Verb) : Prop := ∃ d ∈ v.valency.diatheses, d.controllerRole = some .P

instance (v : Verb) : Decidable (HasAffectee v) :=
  inferInstanceAs (Decidable (∃ d ∈ v.valency.diatheses, _))

namespace PredicateClass

/-- A fragment entry is in a class when it records the property the class is identified by. -/
protected def Mem : PredicateClass → Verb → Prop
  | utterance, v => v.speechActVerb
  | propositionalAttitude, v => v.attitude = some (.doxastic .nonVeridical)
  | commentative, v => v.attitude.bind Attitude.valence ≠ none ∧ v.factivity ≠ none
  | knowledge, v => v.attitude = some (.doxastic .veridical)
  | fearing, v =>
    v.attitude.bind Attitude.valence = some .negative ∧ v.factivity = none ∧ ¬ HasAffectee v
  | desiderative, v =>
    v.attitude.bind Attitude.valence = some .positive ∧ v.factivity = none ∧ ¬ HasAffectee v
  | manipulative, v => HasAffectee v
  | achievement, v => v.implicative ≠ ⊥ ∧ ¬ HasAffectee v
  | phasal, v => v.phasal ≠ none
  | pretence, _ | modal, _ | perception, _ | negative, _ | conjunctive, _ => False

instance : Membership Verb PredicateClass := ⟨PredicateClass.Mem⟩

instance (k : PredicateClass) (v : Verb) : Decidable (v ∈ k) := by
  change Decidable (PredicateClass.Mem k v)
  cases k <;> unfold PredicateClass.Mem <;> infer_instance

end PredicateClass

/-! ### Negative raising -/

/-- The classes whose predicates allow negative raising ([noonan-2007] §2.7). -/
def negativeRaisers : List PredicateClass := [.propositionalAttitude, .desiderative, .modal]

/-- The fragment entries of the verbs of the negative-raising rows. -/
def verbTable : List (String × Verb) :=
  [("think", think.toVerb), ("believe", believe.toVerb), ("want", want.toVerb),
    ("regret", regret.toVerb)]

/-- A negated matrix has the reading with the negation in the complement exactly when its verb is
a propositional attitude, desiderative or modal predicate, as in (214)–(216) and not in (218). -/
theorem lowerNeg_iff : ∀ r ∈ Examples.all, ∃ v ∈ (r.parse? "verb" verbTable).toList,
    (r.readings.lookup "lowerNeg" = some .acceptable ↔ ∃ k ∈ negativeRaisers, v ∈ k) := by
  decide

/-! ### Time reference -/

/-- A complement's time reference is dependent (dtr) when it is a necessary consequence of the
meaning of the ctp, as under *order*, and independent (itr) otherwise, as under *know*
([noonan-2007] §3.1.1). -/
inductive TimeReference where
  | dependent
  | independent
  deriving DecidableEq, Repr

/-- The time reference of the complements of a class, section by section in [noonan-2007] §3.2.
Desideratives divide into usage classes of both kinds, the hope- and wish-classes itr and the
want-class dtr (§3.2.7), and a conjunctive predicate's complement has the one its meaning gives
(§3.2.14). -/
def PredicateClass.timeReference : PredicateClass → Option TimeReference
  | .utterance | .propositionalAttitude | .pretence | .commentative | .knowledge | .fearing =>
    some .independent
  | .manipulative | .modal | .achievement | .phasal | .perception | .negative => some .dependent
  | .desiderative | .conjunctive => none

/-- Reduced complements go with dtr ([noonan-2007] §3.1.2). No English verb of a dtr class takes
an s-like complement. -/
theorem not_isSLike_of_dependent : ∀ k : PredicateClass, k.timeReference = some .dependent →
    ∀ v ∈ verbs, v.toVerb ∈ k → ∀ c ∈ v.codings, ¬ c.IsSLike := by
  decide +kernel

/-- Indicatives go with itr ([noonan-2007] §3.1.2). Every English verb of an itr class whose
complement the fragment codes takes an indicative. -/
theorem indicative_mem_codings_of_independent : ∀ k : PredicateClass,
    k.timeReference = some .independent → ∀ v ∈ verbs, v.toVerb ∈ k → v.codings ≠ [] →
      .indicative ∈ v.codings := by
  decide +kernel

/-- The desiderative *want* takes only a reduced complement and the desiderative *wish* an
indicative, so the class has no one time reference. -/
theorem want_wish_codings : want.toVerb ∈ PredicateClass.desiderative ∧
    wish.toVerb ∈ PredicateClass.desiderative ∧ (∀ c ∈ want.codings, ¬ c.IsSLike) ∧
      .indicative ∈ wish.codings := by
  decide

end Noonan2007
