module

public import Mathlib.Data.Nat.Notation

/-!
# Pesetsky (1995): Zero Syntax

This file formalizes the Cascade account in [pesetsky-1995] of the Target/Subject Matter
restriction on object-experiencer verbs, the impossibility of expressing a Causer together
with a Target or Subject Matter, *the article annoyed Bill at the government*. The verb's
arguments sit in a right-branching Cascade of prepositional projections (`Cascade`), and the
causative reading comes from a zero preposition CAUS, an adjunct-like head situated below the
selected arguments, which is an affix and must have reached the verb by phonological form
(510). Head movement is successive adjunction to each intervening preposition, and a category
headed by a non-affix cannot move on, so CAUS reaches the verb exactly when every preposition
above it is affixal (`canReachV`, `canReachV_append`). The prepositions *at* and *about*
that introduce Target and Subject Matter are not affixes, so CAUS is stranded below them
(`tsm_restriction`), whereas nothing intervenes when the stimulus is absent
(`caus_reaches_without_stimulus`); the same mechanism derives Oehrle's observation that the
causative reading of *give* survives in the double object construction, whose zero
preposition G is an affix, but not with *to* (`oehrle`). Since CAUS starts below the
selected arguments, the Causer originates below the Experiencer and raises to subject, which
is why object-experiencer verbs show backward binding, the experiencer binding into the
reconstructed causer (§6.2.2, `experiencer_ccommands_causer`). The verb classes of
[belletti-rizzi-1988] from which the book's linking problem starts are recorded with the
subject role each predicts (`PsychVerbClass`, `SubjectRole`).

## Implementation notes

Only the prepositions of the restriction and of the double object alternation are
represented. The affixal and prepositional occurrences of CAUS of §6.3, the suppression of
the external argument in (522), the semantics of prepositions and mediated θ-selection of
the fifth chapter, and the account of heavy shift of the seventh are not formalized.

## References

* [pesetsky-1995]
* [belletti-rizzi-1988]
-/

@[expose] public section

namespace Pesetsky1995

/-! ### Cascades -/

/-- A prepositional head of a Cascade: whether it is overt or a zero morpheme, and whether it
is an affix that must join the verb. -/
structure CascadeHead where
  overt : Bool
  affixal : Bool
  deriving DecidableEq

/-- The phrases a Cascade positions. -/
inductive Phrase where
  | experiencer
  | target
  | subjectMatter
  | causer
  | theme
  | goal
  deriving DecidableEq

/-- A Cascade: the right-branching spine of prepositional projections below a verb, each
layer a head with the phrase in its specifier, ending in the complement of the lowest head. -/
inductive Cascade where
  | complement (phrase : Phrase)
  | layer (head : CascadeHead) (spec : Phrase) (rest : Cascade)

/-- The heads from the verb downward. -/
def Cascade.spine : Cascade → List CascadeHead
  | .complement _ => []
  | .layer h _ rest => h :: rest.spine

/-- The position of a phrase, counted from the top, the final complement one below the last
layer. -/
def Cascade.position : Cascade → Phrase → Option ℕ
  | .complement p, q => if p = q then some 0 else none
  | .layer _ spec rest, q => if spec = q then some 0 else (rest.position q).map (· + 1)

/-- A phrase c-commands another when it sits in a higher layer. -/
def Cascade.CCommands (c : Cascade) (p q : Phrase) : Prop :=
  ∃ i j, c.position p = some i ∧ c.position q = some j ∧ i < j

/-- The head at position `i` of a spine can reach the verb by successive adjunction exactly
when every head above it is affixal: adjunction to a non-affix yields a category that cannot
move on, the Head Movement Constraint. -/
def canReachV (spine : List CascadeHead) (i : ℕ) : Prop := ∀ h ∈ spine.take i, h.affixal = true

instance (spine : List CascadeHead) (i : ℕ) : Decidable (canReachV spine i) :=
  inferInstanceAs (Decidable (∀ h ∈ spine.take i, h.affixal = true))

theorem canReachV_append (above : List CascadeHead) (h : CascadeHead)
    (below : List CascadeHead) :
    canReachV (above ++ h :: below) above.length ↔ ∀ h' ∈ above, h'.affixal = true := by
  simp [canReachV]

/-- CAUS: the zero causative preposition, an affix (510). -/
def caus : CascadeHead := ⟨false, true⟩

/-- G: the zero preposition of the double object construction, an affix. -/
def headG : CascadeHead := ⟨false, true⟩

/-- *at*, introducing a Target: overt and not an affix. -/
def headAt : CascadeHead := ⟨true, false⟩

/-- *about*, introducing a Subject Matter: overt and not an affix. -/
def headAbout : CascadeHead := ⟨true, false⟩

/-- *to* of the dative construction: overt and not an affix. -/
def headTo : CascadeHead := ⟨true, false⟩

/-! ### The Target/Subject Matter restriction (§6.2.1) -/

/-- The two roles into which the book divides the object of an emotion: the Target the emotion
is directed at, as in *angry at the government*, and the Subject Matter it is about, as in *worried
about the television set*. -/
inductive StimulusType where
  | target
  | subjectMatter
  deriving DecidableEq, Repr

/-- The preposition that introduces each stimulus type. -/
def stimulusHead : StimulusType → CascadeHead
  | .target => headAt
  | .subjectMatter => headAbout

/-- The phrase of each stimulus type. -/
def stimulusPhrase : StimulusType → Phrase
  | .target => .target
  | .subjectMatter => .subjectMatter

/-- (513): the Experiencer in the specifier of the stimulus preposition, the stimulus in the
specifier of CAUS, and the Causer as CAUS's complement. -/
def stimulusCascade (s : StimulusType) : Cascade :=
  .layer (stimulusHead s) .experiencer (.layer caus (stimulusPhrase s) (.complement .causer))

/-- (514): the Experiencer in the specifier of CAUS, with no stimulus. -/
def plainCascade : Cascade := .layer caus .experiencer (.complement .causer)

theorem stimulusHead_nonaffixal (s : StimulusType) : (stimulusHead s).affixal = false := by
  cases s <;> rfl

theorem tsm_restriction (s : StimulusType) : ¬ canReachV (stimulusCascade s).spine 1 := by
  cases s <;> decide

theorem caus_reaches_without_stimulus : canReachV plainCascade.spine 0 := by decide

/-! ### Oehrle's observation (§6.2.1) -/

/-- (511): the double object construction with a causative reading, G above CAUS. -/
def doubleObjectCascade : Cascade :=
  .layer headG .goal (.layer caus .theme (.complement .causer))

/-- (512): the *to*-dative with CAUS below *to*. -/
def toCascade : Cascade := .layer headTo .theme (.layer caus .goal (.complement .causer))

theorem oehrle : canReachV doubleObjectCascade.spine 1 ∧ ¬ canReachV toCascade.spine 1 := by
  decide

/-! ### Backward binding (§6.2.2) -/

theorem experiencer_ccommands_causer (s : StimulusType) :
    (stimulusCascade s).CCommands .experiencer .causer ∧
      plainCascade.CCommands .experiencer .causer := by
  cases s <;> exact ⟨⟨0, 2, rfl, rfl, by decide⟩, ⟨0, 1, rfl, rfl, by decide⟩⟩

/-! ### The classes of Belletti and Rizzi -/

/-- The classes of [belletti-rizzi-1988] from which the linking problem starts:
experiencer-subject verbs, object-experiencer verbs, and the dative-experiencer verbs of
Italian. -/
inductive PsychVerbClass where
  | classI
  | classII
  | classIII
  deriving DecidableEq

/-- The role of the surface subject. -/
inductive SubjectRole where
  | experiencer
  | stimulus
  deriving DecidableEq

/-- The subject role each class predicts; the dative-experiencer class has no nominative
subject among its two arguments. -/
def PsychVerbClass.expectedSubjectRole : PsychVerbClass → Option SubjectRole
  | .classI => some .experiencer
  | .classII => some .stimulus
  | .classIII => none

end Pesetsky1995
