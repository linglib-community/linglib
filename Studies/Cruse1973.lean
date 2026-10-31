module

public import Linglib.Semantics.ArgumentStructure.EnergySource
public import Linglib.Data.Examples.Cruse1973
public import Linglib.Data.Examples.Readers

/-!
# Cruse (1973): Some thoughts on agentivity

Cruse replaces the referential definitions of agentivity, Fillmore's animate perceived
instigator and Gruber's wilful source, by an entailment test: a noun is a doer in a sentence
when the sentence entails that the noun did something. The test admits inanimate doers,
process verbs and statives, against the received opinions, and what it detects is
heterogeneous: at least four features each suffice for doing, the volitive, the effective, the
initiative and the agentive, an instrument bearing none of them, and each has contextual
diagnostics of its own.

A noun's profile is the set of features its sentence attributes to it, so a doer is a noun with
a nonempty profile. The paper's examples are checked against the normality each frame predicts
from the profile, the three received opinions are refuted among them, and Gruber's criteria of
agentivity, as the paper reanalyzes them, pick out strictly nested classes of nouns.

## Implementation notes

* The agentive and the effective are the features of a force bearer drawing on its own energy
  and on energy imparted to it; `isSelfEnergetic_iff_exists_energySource_eq` identifies them
  with the self-energetic sources of `EnergySource`. An instrumental bears no feature.
* The paper's query mark is printed as `?`; it defines the mark as clear abnormality, so a
  marked example counts as abnormal.
* The paper leaves open the contexts that neutralize *do* and *happen*, and its examples in
  them are outside the model.

## References

* [D. A. Cruse, *Some thoughts on agentivity* (1973)][cruse-1973]
* [C. J. Fillmore, *The case for case* (1968)][fillmore-1968]
* [J. S. Gruber, *Look and see* (1967)][gruber-1967]
* [M. A. K. Halliday, *Notes on transitivity and theme in English: part 1*
  (1967)][halliday-1967]
* [M. A. K. Halliday, *Notes on transitivity and theme in English: part 3*
  (1968)][halliday-1968]
* [J. Lyons, *Structural semantics* (1963)][lyons-1963]
* [J. Lyons, *Introduction to theoretical linguistics* (1968)][lyons-1968]
* [J. M. Anderson, *The grammar of case* (1971)][anderson-1971]
* [W. L. Chafe, *Meaning and the structure of language* (1970)][chafe-1970]
-/

@[expose] public section

namespace Cruse1973

open ArgumentStructure

/-- The features whose presence makes a noun a doer. -/
inductive Feature where
  /-- An act of will is stated or implied. -/
  | volitive
  /-- The noun exerts a force by virtue of its position or motion, not of its own energy. -/
  | effective
  /-- The noun initiates the action by giving a command. -/
  | initiative
  /-- The noun uses its own energy in carrying out the action. -/
  | agentive
  deriving DecidableEq, Fintype

/-- The energy source a feature attributes to a force bearer. -/
def Feature.energySource : Feature → Option EnergySource
  | .agentive => some .internal
  | .effective => some .imparted
  | .volitive | .initiative => none

theorem isSelfEnergetic_iff_exists_energySource_eq (s : EnergySource) :
    s.IsSelfEnergetic ↔ ∃ f : Feature, f.energySource = some s := by
  cases s <;> decide

/-- The features a sentence attributes to a noun in relation to its verb. -/
abbrev Profile := Finset Feature

/-- The frames the paper places a sentence in. -/
inductive Frame where
  /-- *What X did was …*, for a subject. -/
  | doForm
  /-- *What happened to X was that …*, for a subject. -/
  | happenForm
  /-- *X VP entails X did something*, or the normality of *X VP: it therefore follows that X did
  something*, for a subject or an object. -/
  | entails
  /-- A purpose phrase *in order to …*. -/
  | purpose
  /-- The imperative. -/
  | imperative
  /-- Modification by *carefully*. -/
  | carefully
  /-- Reflexivization of an ergative verb used intransitively, or *V oneself Adj* for a
  non-ergative, with minor rather than considerable semantic effects. -/
  | reflexive
  /-- A manner adverb of energy output, *powerfully*, *vigorously* or *energetically*, for
  gross physical actions. -/
  | manner
  /-- Transitive *fly* with the noun as its object. -/
  | causative
  /-- A context denying a precondition of initiation by command. -/
  | initiativeDenial
  /-- The progressive form, Lyons's criterion for stativity. -/
  | progressive
  /-- The sentence itself. -/
  | plain
  deriving DecidableEq

/-- Normality of a sentence in a frame as the paper's diagnostics predict it from the noun's
profile. The paper claims only that each feature suffices for the *do* form; that a noun with
no feature is no doer is read off its happen-sentences. The progressive tests the verb's
stativity, on which the profile places no constraint. -/
def Frame.Normal : Frame → Profile → Prop
  | .doForm, p | .entails, p => p.Nonempty
  | .happenForm, p => p = ∅
  | .purpose, p | .imperative, p => .volitive ∈ p
  | .carefully, p => .volitive ∈ p ∧ .agentive ∈ p
  | .reflexive, p | .manner, p | .causative, p => .agentive ∈ p
  | .initiativeDenial, p => .initiative ∉ p
  | .progressive, _ | .plain, _ => True

instance (t : Frame) : DecidablePred t.Normal := fun _ ↦ by
  cases t <;> unfold Frame.Normal <;> infer_instance

/-- Lyons's verb classes at issue in the received opinions. -/
inductive VerbClass where
  /-- An obligatorily process verb, *die*. -/
  | process
  /-- A stative verb, *stand*, *have*. -/
  | stative
  deriving DecidableEq

/-! ### Gruber's criteria -/

theorem carefully_lt_purpose_lt_doForm :
    Frame.carefully.Normal < Frame.purpose.Normal ∧ Frame.purpose.Normal < Frame.doForm.Normal :=
  ⟨lt_of_le_not_ge (fun _ h ↦ h.1) fun h ↦ absurd (h {.volitive} (by decide)) (by decide),
    lt_of_le_not_ge (fun _ h ↦ ⟨_, h⟩) fun h ↦ absurd (h {.agentive} (by decide)) (by decide)⟩

/-! ### The paper's examples -/

/-- The frames by their `paperFeatures` labels. -/
def Frame.labels : List (String × Frame) :=
  [("do", .doForm), ("happen", .happenForm), ("entails", .entails), ("purpose", .purpose),
   ("imperative", .imperative), ("carefully", .carefully), ("reflexive", .reflexive),
   ("manner", .manner), ("causative", .causative), ("initiativeDenial", .initiativeDenial),
   ("progressive", .progressive), ("plain", .plain)]

/-- The profiles by their `paperFeatures` labels; an instrumental bears no feature. -/
def Profile.labels : List (String × Profile) :=
  [("", ∅), ("volitive", {.volitive}), ("initiative", {.initiative}), ("agentive", {.agentive}),
   ("effective", {.effective}), ("instrumental", ∅), ("volitive+agentive", {.volitive, .agentive})]

/-- An example of the paper, with its frame, the profile of its noun, its judgment, and whether
it states that an entailment fails. -/
structure Row where
  frame : Frame
  /-- The profile attributed to the noun, if any; the stative and some ambiguous examples carry
  none. -/
  profile : Option Profile
  /-- Whether the attribution is the study's rather than the paper's. -/
  inferred : Bool
  /-- Whether the noun is marked inanimate. -/
  inanimate : Bool
  /-- The verb's class, where a received opinion is at issue. -/
  verbClass : Option VerbClass
  /-- Whether *do* and *happen* are neutralized, as in *why does the door do that*. -/
  neutralized : Bool
  judgment : Judgment
  /-- The example states that the entailment fails, *X VP does not entail X did something*. -/
  denied : Bool

/-- An example read into its frame, profile and judgment. -/
def Row.ofDatum (e : Datum) : Option Row := do
  pure { frame := ← e.parse? "frame" Frame.labels
         profile := e.parse? "features" Profile.labels
         inferred := decide (e.feature? "inferred" = some "true")
         inanimate := decide (e.feature? "animate" = some "false")
         verbClass := e.parse? "verbClass" [("process", .process), ("stative", .stative)]
         neutralized := decide (e.feature? "neutralized" = some "true")
         judgment := e.judgment
         denied := decide (e.feature? "entailment" = some "denied") }

theorem isSome_ofDatum : ∀ e ∈ Examples.all, (Row.ofDatum e).isSome := by decide

/-- The paper's examples. -/
def data : List Row := Examples.all.filterMap Row.ofDatum

theorem acceptable_iff_normal : ∀ d ∈ data, d.neutralized = false →
    ∀ p ∈ d.profile, (d.judgment = .acceptable ∧ d.denied = false ↔ d.frame.Normal p) := by
  decide

theorem exists_neutralized_doForm : ∃ d ∈ data, d.neutralized = true ∧ d.profile = some ∅ ∧
    d.frame = .doForm ∧ d.judgment = .acceptable := by
  decide

/-! ### Against the received opinions -/

theorem exists_inanimate_doer :
    ∃ d ∈ data, d.inanimate = true ∧ d.frame = .doForm ∧ d.judgment = .acceptable := by decide

theorem exists_process_doer :
    ∃ d ∈ data, d.verbClass = some .process ∧ d.frame = .doForm ∧ d.judgment = .acceptable := by
  decide

theorem exists_stative_doer :
    ∃ d ∈ data, d.verbClass = some .stative ∧ d.frame = .doForm ∧ d.judgment = .acceptable := by
  decide

/-! ### The heterogeneity of doing -/

theorem exists_doer_of_feature : ∀ f ∈ [Feature.volitive, .effective], ∃ d ∈ data,
    d.inferred = false ∧ d.profile = some {f} ∧ d.frame = .doForm ∧ d.judgment = .acceptable := by
  decide

end Cruse1973
