module

public import Linglib.Discourse.SpeechAct
public import Linglib.Semantics.Mood.SpeechEvent
public import Linglib.Fragments.Romance.French.Modals
public import Linglib.Data.Examples.RuytenbeekEtAl2017
public import Linglib.Data.Statistics.RuytenbeekEtAl2017

/-!
# Ruytenbeek et al. (2017): Indirect request processing, sentence types and illocutionary forces

This file formalizes the paper's test of speech-act literalism, on which a sentence type
encodes an illocutionary force, so that a directive reading of a non-imperative sentence is
secondary, mediated by the encoded force, unless the construction is a conventionalised
indirect request. Non-literalism instead makes a directive reading primary whenever the
sentence shares the semantic features that make imperatives suited to directives: the deontic
necessity of [kaufmann-2012]'s imperative, the questioning of the addressee's ability that is
[clark-1979]'s convention of means, or the enablement the possibility modals encode. The
two accounts are predicates on the constructions of the paper's two French experiments
(`Literalist.DirectivePrimary`, `NonLiteralist.DirectivePrimary`), with conventionalisation
read off the paper's corpus counts and the modal semantics off the French fragment. In both
experiments directive interpretations came with no fixations on the answer buttons and with
response times matching the imperative, and they came for exactly the constructions
non-literalism predicts (`nonLiteralist_predicts`); the non-conventionalised *Est-il possible
de VP?* and the deontic *Vous devez VP* received them although literalism makes those
readings secondary (`literalist_refuted`).

## Implementation notes

The corpus counts, the response-time estimates and the paper's findings on each construction's
interpretations are `Data/Statistics/RuytenbeekEtAl2017`; the stimulus sentences are
`Data/Examples/RuytenbeekEtAl2017.json`. A construction is directive when it received directive
interpretations at all, and unactivated when the paper reports no fixations on the answer buttons
and response times equal to the imperative's for those interpretations; the regression
coefficients stay in prose.
The paper's ranking of directive rates, *Vous devez* above *Vous pouvez* above *Il est
possible*, which it attributes to the permission reading of *pouvoir*, is not derived.

## References

* [ruytenbeek-etal-2017]
* [kaufmann-2012]
* [clark-1979]
* [sadock-zwicky-1985]
* [talmy-2000]
-/

@[expose] public section

namespace RuytenbeekEtAl2017

open Discourse.SpeechAct French
open Modality
open Discourse.SpeechAct.Force (primaryFlavor)

/-! ### Constructions and forces -/

/-- The sentence type of a construction; its interrogatives are polar questions. -/
def Construction.sentenceType : Construction → Clause.SentenceType
  | .imperative => .imperative
  | .controlInterrogative | .canYou | .isItPossible => .polar
  | .youMust | .youCan | .itIsPossible | .controlDeclarative => .declarative

/-- The modal of a construction, from the French fragment. -/
def Construction.modal : Construction → Option ModalItem
  | .canYou | .youCan => some pouvoir
  | .isItPossible | .itIsPossible => some ilEstPossibleDe
  | .youMust => some devoir
  | _ => none

/-- The preparatory condition a construction questions, which for the two interrogative
requests is the addressee's ability. -/
def Construction.queriedPrep : Construction → Option PreparatoryCondition
  | .canYou | .isItPossible => some .ability
  | _ => none

/-! ### The corpus and conventionalisation -/

/-- The interrogative request of the corpus count a construction instantiates. -/
def Construction.form : Construction → Option Form
  | .canYou => some .pouvezVous
  | .isItPossible => some .estIlPossible
  | _ => none

/-- A construction is conventionalised as a request when it is counted in the corpus and its
directive uses outnumber its question uses there. -/
def Conventionalised (c : Construction) : Prop :=
  ∃ f ∈ c.form, (corpus f).genuineQuestion < (corpus f).indirectRequest

instance (c : Construction) : Decidable (Conventionalised c) := by
  unfold Conventionalised; infer_instance

theorem conventionalised : Conventionalised .canYou ∧ ¬ Conventionalised .isItPossible := by
  decide +kernel

/-! ### The two accounts -/

/-- Under literalism a directive reading is primary only when the sentence type encodes
directive force or the construction is a conventionalised indirect request; any other
directive reading is secondary and activates the encoded force. -/
def Literalist.DirectivePrimary (c : Construction) : Prop :=
  c.sentenceType.force = .directive ∨ Conventionalised c

/-- Under non-literalism a directive reading is primary when the construction shares the
imperative's directive-making semantics: the imperative's own deontic necessity, the
questioning of the addressee's ability, or a possibility modal's enablement. -/
def NonLiteralist.DirectivePrimary (c : Construction) : Prop :=
  c.sentenceType = .imperative ∨
    (∃ m ∈ c.modal, ∃ φ ∈ primaryFlavor .directive, (.necessity, φ) ∈ m.meaning) ∨
    c.queriedPrep = some .ability ∨ ∃ m ∈ c.modal, .possibility ∈ m.forces

instance (c : Construction) : Decidable (Literalist.DirectivePrimary c) := by
  unfold Literalist.DirectivePrimary; infer_instance

instance (c : Construction) : Decidable (NonLiteralist.DirectivePrimary c) := by
  unfold NonLiteralist.DirectivePrimary; infer_instance

theorem accounts_differ (c : Construction) :
    (Literalist.DirectivePrimary c ↔ NonLiteralist.DirectivePrimary c) ↔
      c.modal = none ∨ Conventionalised c := by
  cases c <;> decide +kernel

/-! ### The observations -/

/-- The construction received directive interpretations. -/
def Directive (r : Interpretation) : Prop := r.directive ≠ .never

instance (r : Interpretation) : Decidable (Directive r) := by unfold Directive; infer_instance

/-- The directive interpretations came without activation of the encoded force, with no
fixations on the answer buttons and response times equal to the imperative's. -/
def Unactivated (r : Interpretation) : Prop := r.answerActivity = some .no

instance (r : Interpretation) : Decidable (Unactivated r) := by unfold Unactivated; infer_instance

theorem directive_unactivated : ∀ r ∈ interpretations, Directive r → Unactivated r := by
  decide +kernel

theorem nonLiteralist_predicts :
    ∀ r ∈ interpretations, Directive r ↔ NonLiteralist.DirectivePrimary r.construction := by
  decide +kernel

theorem literalist_refuted :
    ∀ r ∈ interpretations, ¬ Literalist.DirectivePrimary r.construction → Directive r →
      Unactivated r := by
  decide +kernel

theorem literalist_secondary_found :
    ∀ c, c = .isItPossible ∨ c = .youMust ∨ c = .youCan ∨ c = .itIsPossible →
      ¬ Literalist.DirectivePrimary c ∧
        ∃ r ∈ interpretations, r.construction = c ∧ Directive r := by
  decide +kernel

/-- The estimated response time of a response to a construction in a study, in milliseconds,
when the paper reports one. -/
def rt (s : Study) (c : Construction) (r : Response) : Option ℕ :=
  (responseTimes.find? fun x ↦ x.study = s ∧ x.construction = c ∧ x.response = r).map (·.estimate)

theorem canYou_question_slower :
    ∃ a ∈ rt .one .controlInterrogative .yes, ∃ b ∈ rt .one .canYou .yes, a < b := by
  decide +kernel

end RuytenbeekEtAl2017
