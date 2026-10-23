module

public import Linglib.Semantics.ConventionalImplicature
public import Linglib.Discourse.Commitment.Basic
public import Linglib.Data.Examples.HarrisPotts2009

/-!
# Harris and Potts (2009): Perspective-shifting with appositives and expressives

Harris and Potts account for whose commitments an appositive or expressive expresses. Potts's
two-dimensional meaning is kept, but the conventional-implicature content carries a free orientation
variable, resolved in discourse to the speaker or to another participant (`CIItem.resolve`).
Orientation is public commitment, since an utterance commits the speaker to the at-issue content and
whoever the item is oriented to to the implicature (`CIItem.utter`), so under a non-speaker-oriented
reading the speaker's commitment set narrows by the at-issue content alone
(`commitmentSet_utter_speaker_other`). Against the configurational hypothesis, on which non-speaker
orientation is semantic binding by an attitude predicate (10a), the paper sets the contextual one
(10b), on which speaker orientation is a default that pragmatic factors override in any syntactic
position. The attested readings and the items of the two experiments are the rows of
`Data/Examples/HarrisPotts2009.json`, and `not_configurational` is the paper's refutation, since
(11) and (12) are epithets in matrix clauses read from another's perspective. Experiment 1 extends
this to appositives, read as the attitude subject's in 68% of unembedded and 86% of embedded trials,
so that embedding facilitates the shift without being required for it; Experiment 2 finds a negative
context raising subject-oriented readings of a matrix epithet from 7% to 17%; and the corpus study
finds speaker orientation dominant, in 32 of the 34 embedded appositive relatives with agreed
textual evidence.

## Implementation notes

The commitment state is `Commitment.State` over `Orientation`, so the values of the orientation
variable are exactly the possible committers. The `Both` response of the experiments, which the
paper reads as pragmatic enrichment of one attribution, is recorded in the rows but not
modelled, and the regression models of §3.3 and §4.3 stay in prose. The rows of the
experimental items carry their conditions, not the per-item response counts, which the paper
reports only in aggregate.

## References

* [harris-potts-2009]
* [potts-2005]
* [amaral-roberts-smith-2007]
-/

@[expose] public section

namespace HarrisPotts2009

open ConventionalImplicature (TwoDim)
open Commitment

/-- A conventional implicature expresses the commitment of the speaker or of another discourse
participant. -/
inductive Orientation (Person : Type) where
  | speaker
  | other (p : Person)
  deriving DecidableEq, Repr

/-- An appositive or expressive has at-issue content and conventional-implicature content that
depends on the value of the orientation variable, resolved in discourse. -/
structure CIItem (Person W : Type) where
  /-- The conventional implicature under each orientation. -/
  ciFor : Orientation Person → W → Prop
  /-- The at-issue content, which does not depend on the orientation. -/
  atIssue : W → Prop

variable {Person W : Type} (item : CIItem Person W)

/-- The two-dimensional meaning once the orientation variable is resolved to `o`. -/
def CIItem.resolve (o : Orientation Person) : TwoDim W (W → Prop) :=
  { atIssue := item.atIssue, notAtIssue := item.ciFor o }

/-- Orientation is public commitment (§1), so uttering the item with its orientation resolved to
`o` commits the speaker to the at-issue content and `o` to the conventional implicature. -/
def CIItem.utter (o : Orientation Person) (K : State (Orientation Person) W) :
    State (Orientation Person) W :=
  insert (.speaker, {w | item.atIssue w}) (insert (o, {w | item.ciFor o w}) K)

variable (K : State (Orientation Person) W)

theorem commitmentSet_utter_speaker :
    (item.utter .speaker K).commitmentSet .speaker =
      {w | item.atIssue w} ∩ ({w | item.ciFor .speaker w} ∩ K.commitmentSet .speaker) := by
  simp [CIItem.utter]

/-- A non-speaker-oriented reading adds only the at-issue content to the speaker's commitments, as
with the appositive of (8) and the expressive of (9). -/
theorem commitmentSet_utter_speaker_other (p : Person) :
    (item.utter (.other p) K).commitmentSet .speaker =
      {w | item.atIssue w} ∩ K.commitmentSet .speaker := by
  simp [CIItem.utter, State.commitmentSet_insert_of_ne]

theorem commitmentSet_utter_other (p : Person) :
    (item.utter (.other p) K).commitmentSet (.other p) =
      {w | item.ciFor (.other p) w} ∩ K.commitmentSet (.other p) := by
  simp [CIItem.utter, State.commitmentSet_insert_of_ne]

/-! ### The configurational and the contextual hypothesis (10) -/

/-- The response categories of (13) and (16) record whose view the content was taken to be. -/
inductive Response where
  | speaker
  | subject
  | both
  deriving DecidableEq, Repr

/-- An attested reading records whether the item sits in the complement of an attitude or speech
predicate and to whom its content was attributed. -/
structure Reading where
  embedded : Bool
  response : Response
  deriving DecidableEq, Repr

/-- The response category of a row's `orientation` feature. -/
def responseOfLabel : String → Option Response
  | "speaker" => some .speaker
  | "subject" => some .subject
  | "both" => some .both
  | _ => none

/-- Read a reading off a row that records an attribution. -/
def Reading.ofDatum (ex : Datum) : Option Reading := do
  let e ← ex.feature? "embedded"
  let r ← ex.feature? "orientation" >>= responseOfLabel
  pure ⟨e == "yes", r⟩

/-- The attested readings of §2 and §5. -/
def readings : List Reading := Examples.all.filterMap Reading.ofDatum

/-- Non-speaker orientation arises only by semantic binding under an attitude predicate, so an
unembedded item is read as the speaker's (10a). -/
def Configurational (D : List Reading) : Prop :=
  ∀ r ∈ D, r.response ≠ .speaker → r.embedded = true

/-- An epithet in a matrix clause read from another's perspective (11) and (12). -/
theorem exists_unembedded_subject :
    ∃ r ∈ readings, r.embedded = false ∧ r.response = .subject := by decide

/-- The attested readings refute the configurational hypothesis, leaving the contextual hypothesis
of (10b). -/
theorem not_configurational : ¬ Configurational readings := λ h =>
  have ⟨r, hr, he, hs⟩ := exists_unembedded_subject
  by simpa [he, hs] using h r hr

end HarrisPotts2009
