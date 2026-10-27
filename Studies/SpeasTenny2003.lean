module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Reference.Logophoricity

/-!
# Speas & Tenny (2003): Configurational Properties of Point of View Roles

Speas and Tenny derive the pragmatic roles a grammar can refer to from argument positions. The
speech-act head projects a shell with the speaker as its external argument, the utterance content
as the specifier of the lower head and the hearer as its complement, the agent, theme and goal of
the speech act. The head has two formal features: absorbing the feature checked in a spec-head
configuration promotes the hearer above the content, and the head selects a finite or a nonfinite
content. A second shell, the sentience domain, hosts the seat of knowledge, the sentient argument
that evaluates the proposition, and the evidence below it. The seat is controlled by the closest
c-commander of the content.

## Implementation notes

* The speech-act shell is recorded by the height of each argument (`SAFeatures.height`), and
  c-command is comparison of heights.
* Whether a quotative mood is the speech-act structure with an expletive speaker, which the paper
  leaves open, and the parallel it draws between the logophoric hierarchy of predicates and the
  hierarchy of evidence types are not formalized.
* The speech-act projection carries no specific predicate, only the configuration, so this is not
  the performative analysis of Ross.

## References

* [speas-tenny-2003]
* [hale-keyser-1993]
* [cinque-1999]
* [rizzi-1997]
* [larson-1988]
* [searle-1979]
* [sells-1987]
* [ross-1970]
* [willett-1988]
-/

@[expose] public section

namespace SpeasTenny2003

/-! ### The speech-act shell -/

/-- The arguments of the speech-act head, the agent, theme and goal of the speech act. -/
inductive SAArgument where
  | speaker
  | content
  | hearer
  deriving DecidableEq, Fintype, Repr

/-- The speech-act head has two formal features. One says whether the feature checked in a spec-head
configuration is absorbed, promoting the hearer above the content, and the other whether the head
selects a finite content. -/
structure SAFeatures where
  hearerPromoted : Bool
  contentFinite : Bool
  deriving DecidableEq, Repr

/-- The height of an argument in the shell. The speaker is the external argument, and below it the
content precedes the hearer unless the hearer is promoted. -/
def SAFeatures.height (f : SAFeatures) : SAArgument → ℕ
  | .speaker => 2
  | .content => if f.hearerPromoted then 0 else 1
  | .hearer => if f.hearerPromoted then 1 else 0

/-- `a` c-commands `b` in the shell when `a` sits higher. -/
def SAFeatures.CCommands (f : SAFeatures) (a b : SAArgument) : Prop := f.height b < f.height a

instance (f : SAFeatures) (a b : SAArgument) : Decidable (f.CCommands a b) :=
  inferInstanceAs (Decidable (_ < _))

/-- The controller of the seat of knowledge is the hearer once promoted and the speaker
otherwise. -/
def SAFeatures.controller (f : SAFeatures) : SAArgument :=
  if f.hearerPromoted then .hearer else .speaker

theorem SAFeatures.controller_cCommands (f : SAFeatures) : f.CCommands f.controller .content := by
  rcases f with ⟨_ | _, _ | _⟩ <;> decide

/-- The controller is the closest c-commander of the content, since any other argument c-commanding
the content c-commands the controller. -/
theorem SAFeatures.controller_closest (f : SAFeatures) {a : SAArgument}
    (h : f.CCommands a .content) (ha : a ≠ f.controller) : f.CCommands a f.controller := by
  rcases f with ⟨_ | _, _⟩ <;> cases a <;> simp_all [SAFeatures.CCommands, SAFeatures.height,
    SAFeatures.controller]

theorem SAFeatures.controller_eq_hearer_iff (f : SAFeatures) :
    f.controller = .hearer ↔ f.CCommands .hearer .content := by
  rcases f with ⟨_ | _, _ | _⟩ <;> decide

/-! ### The four moods -/

/-- The grammaticized moods. -/
inductive Mood where
  | declarative
  | interrogative
  | imperative
  | subjunctive
  deriving DecidableEq, Fintype, Repr

/-- The mood a feature setting yields. A finite content with the hearer in place is a declarative
and with the hearer promoted an interrogative; a nonfinite content with the hearer promoted is an
imperative and with the content above the hearer a subjunctive. -/
def Mood.ofFeatures : SAFeatures → Mood
  | ⟨false, true⟩ => .declarative
  | ⟨true, true⟩ => .interrogative
  | ⟨true, false⟩ => .imperative
  | ⟨false, false⟩ => .subjunctive

/-- The feature setting of a mood. -/
def Mood.features : Mood → SAFeatures
  | .declarative => ⟨false, true⟩
  | .interrogative => ⟨true, true⟩
  | .imperative => ⟨true, false⟩
  | .subjunctive => ⟨false, false⟩

theorem Mood.ofFeatures_features (m : Mood) : Mood.ofFeatures m.features = m := by
  cases m <;> rfl

theorem Mood.features_ofFeatures (f : SAFeatures) : (Mood.ofFeatures f).features = f := by
  rcases f with ⟨_ | _, _ | _⟩ <;> rfl

/-- The inventory of grammaticized moods exhausts the variation of the head's two features and
nothing else, which is why no language marks any further speech act. -/
def moodEquiv : SAFeatures ≃ Mood :=
  ⟨Mood.ofFeatures, Mood.features, Mood.features_ofFeatures, Mood.ofFeatures_features⟩

/-! ### The sentience domain and the pragmatic roles -/

/-- The arguments of the sentience shell are, from highest, the seat of knowledge in the specifier
of the evaluation phrase, the evidence in the specifier of the evidential phrase, and the
proposition. -/
inductive SentienceArgument where
  | seatOfKnowledge
  | evidence
  | proposition
  deriving DecidableEq, Fintype, Repr

/-- The grammatically relevant pragmatic roles are the sentient argument positions of the two
shells, no more than three in any language. -/
inductive PRole where
  | speaker
  | hearer
  | seatOfKnowledge
  deriving DecidableEq, Fintype, Repr

/-- The argument the seat of knowledge is coindexed with in a mood, its controller. -/
def Mood.seatOfKnowledge (m : Mood) : SAArgument := m.features.controller

/-- The speaker is the seat in declaratives and subjunctives, the hearer in interrogatives and
imperatives. The hearer holds the knowledge that settles a question and is responsible for realizing
the unrealized content of a command, the speaker for choosing the preferred world of a
subjunctive. -/
theorem Mood.seatOfKnowledge_eq :
    Mood.declarative.seatOfKnowledge = .speaker ∧ Mood.interrogative.seatOfKnowledge = .hearer ∧
    Mood.imperative.seatOfKnowledge = .hearer ∧ Mood.subjunctive.seatOfKnowledge = .speaker := by
  decide

theorem Mood.seatOfKnowledge_eq_hearer_iff (m : Mood) :
    m.seatOfKnowledge = .hearer ↔ m.features.hearerPromoted = true := by
  cases m <;> decide

theorem Mood.seatOfKnowledge_ne_content (m : Mood) : m.seatOfKnowledge ≠ .content := by
  cases m <;> decide

/-- The position each logophoric role of [sells-1987] is. The source is the highest argument of
the speech act, the self is the seat of knowledge, and the pivot is a thematic argument coindexed
with the seat, an experiencer when a theme and the orientation of a predicate like *come* when a
goal. -/
def target : LogophoricRole → PRole
  | .source => .speaker
  | .self => .seatOfKnowledge
  | .pivot => .seatOfKnowledge

/-- No logophoric role is a role of its own, since each is a coindexing with the speaker or the
seat. -/
theorem target_ne_hearer (r : LogophoricRole) : target r ≠ .hearer := by
  cases r <;> decide

end SpeasTenny2003
