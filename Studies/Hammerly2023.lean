module

public import Studies.Harbour2016

/-!
# Hammerly (2023): A set-based semantics for person, obviation, and animacy

[hammerly-2023] derives the person partitions from bivalent features denoting first-order
predicates, following the contrastive account of [cowper-hall-2019]. A feature denotes a set of
ontological primitives, [Author] the speaker and [Participant] the speaker and the addressee
(21), and composes with a lattice of referents by keeping those containing some member of that
set or those containing none (24). Which features are active, and how they are read, follows from
the successive division algorithm (26): a learner divides the inventory feature by feature until
every category is distinguished, and a feature applies only where it makes a contrast (28), (29).
Under [+Author] the participant feature makes no contrast, since every referent there contains
the speaker, so a learner facing a clusivity contrast narrows it to [Participant*], 'includes a
participant other than the speaker', in effect an addressee feature (p. 55). The account derives
all and only the five partitions of [harbour-2016] (p. 55). Since [Participant] and
[Participant*] are never active together, the tripartition grouping inclusive with second person,
which a free addressee feature would generate, is excluded ((60), p. 72).

## Main definitions

* `Hammerly2023.Feature`: [Author], [Participant] and the narrowed [Participant*].
* `Hammerly2023.divide`, `Hammerly2023.sda`: the successive division algorithm.
* `Hammerly2023.Admissible`: a contrastive hierarchy whose features all contrast and whose
  narrowing is licensed.

## Main results

* `image_graph_sda_eq_geometry`: the admissible hierarchies derive exactly the partitions
  Harbour's bivalent geometry (9) generates, his five.
* `sda_participant_author`, `sda_author_participantStar`: the hierarchies of Figures 4 and 5,
  the tripartition and the quadripartition.
* `not_admissible_participant_participantStar`, `not_admissible_participantStar`: narrowing
  alongside the wide feature, or where the wide feature contrasts, is not licensed.

## Implementation notes

Only the core persons of §3 are formalized, on participant sets, with the obviation and animacy
features of §4 left aside. A hierarchy is a list of features, its order the contrastive scope;
since the features denote first-order predicates, their order of composition does not matter
(p. 52). Narrowing is licensed where the wide [Participant] would leave some cell undivided,
the situation of the [+Author] cell in Figure 5.

## References

* [hammerly-2023]
* [cowper-hall-2019]
* [harbour-2016]
-/

@[expose] public section

namespace Hammerly2023

open Discourse Finset

/-! ### Features as first-order predicates (§3.1) -/

/-- The person features: [Author], [Participant], and [Participant*], the participant feature
narrowed under [+Author] (p. 55). -/
inductive Feature where
  | author
  | participant
  | participantStar
  deriving DecidableEq, Fintype, Repr

/-- The set a feature denotes (21): the speaker for [Author], the speaker and the addressee for
[Participant], and the addressee alone for [Participant*]. -/
def Feature.denotation : Feature → Finset Role
  | .author => {.speaker}
  | .participant => {.speaker, .addressee}
  | .participantStar => {.addressee}

/-- Positive composition keeps the referents containing some member of the feature's set (24a);
negative composition keeps the others (24b). -/
def Feature.Positive (f : Feature) (s : Finset Role) : Prop := (s ∩ f.denotation).Nonempty

instance (f : Feature) : DecidablePred f.Positive := fun _ ↦ by
  unfold Feature.Positive; infer_instance

/-- [Author] is the author feature of `Person.Bears`. -/
theorem Feature.positive_author_iff (s : Finset Role) :
    Feature.author.Positive s ↔ Person.Bears s .author := by
  revert s; decide

/-- [Participant] is the participant feature of `Person.Bears`, since every role is a speech-act
participant. -/
theorem Feature.positive_participant_iff (s : Finset Role) :
    Feature.participant.Positive s ↔ Person.Bears s .participant := by
  revert s; decide

/-! ### The successive division algorithm (§3.2) -/

/-- A feature makes a contrast in a cell when it holds of some of its members and fails of
others (28). -/
def Contrasts (f : Feature) (c : Finset (Finset Role)) : Prop :=
  (c.filter f.Positive).Nonempty ∧ (c.filter (¬ f.Positive ·)).Nonempty

instance (f : Feature) : DecidablePred (Contrasts f) := fun _ ↦ by
  unfold Contrasts; infer_instance

/-- A feature divides a cell into its positive and negative parts where it makes a contrast,
and leaves it whole otherwise. -/
def divide (f : Feature) (c : Finset (Finset Role)) : List (Finset (Finset Role)) :=
  if Contrasts f c then [c.filter f.Positive, c.filter (¬ f.Positive ·)] else [c]

/-- The cells a contrastive hierarchy derives (26): starting from the whole person space, each
feature in turn divides every current cell. -/
def sda (h : List Feature) : List (Finset (Finset Role)) :=
  h.foldl (fun cells f ↦ cells.flatMap (divide f)) [univ]

/-- A hierarchy is admissible from the current cells when each feature contrasts in some cell
(29), and [Participant*] occurs only where the wide [Participant] would leave some cell
undivided (p. 55). -/
def AdmissibleFrom : List (Finset (Finset Role)) → List Feature → Prop
  | _, [] => True
  | cells, f :: h =>
    (∃ c ∈ cells, Contrasts f c) ∧
      (f = .participantStar → ∃ c ∈ cells, c.card ≥ 2 ∧ ¬ Contrasts .participant c) ∧
      AdmissibleFrom (cells.flatMap (divide f)) h

instance instDecidableAdmissibleFrom :
    ∀ cells h, Decidable (AdmissibleFrom cells h)
  | _, [] => isTrue trivial
  | cells, f :: h =>
    have := instDecidableAdmissibleFrom (cells.flatMap (divide f)) h
    inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- An admissible contrastive hierarchy: no feature twice, never [Participant] and
[Participant*] together, and admissible from the undivided person space. -/
def Admissible (h : List Feature) : Prop :=
  h.Nodup ∧ ¬ (.participant ∈ h ∧ .participantStar ∈ h) ∧ AdmissibleFrom [univ] h

instance : DecidablePred Admissible := fun _ ↦ by unfold Admissible; infer_instance

/-- The contrastive hierarchies over the three features: every ordering of every subset. -/
def hierarchies : List (List Feature) :=
  [Feature.author, .participant, .participantStar].sublists.flatMap List.permutations'

/-- The graph of a partition given by its cells, as a finset of pairs of participant sets. -/
def cellGraph (cells : List (Finset (Finset Role))) : Finset (Finset Role × Finset Role) :=
  univ.filter fun p ↦ ∃ c ∈ cells, p.1 ∈ c ∧ p.2 ∈ c

/-! ### The derived partitions -/

/-- Figure 4: [Participant] over [Author] gives the tripartition. -/
theorem sda_participant_author :
    sda [.participant, .author] = [{{.speaker}, {.speaker, .addressee}}, {{.addressee}}, {∅}] := by
  decide

/-- Figure 5: [Author] over the narrowed [Participant*] gives the quadripartition. -/
theorem sda_author_participantStar :
    sda [.author, .participantStar] =
      [{{.speaker, .addressee}}, {{.speaker}}, {{.addressee}}, {∅}] := by
  decide

theorem admissible_author_participantStar : Admissible [.author, .participantStar] := by decide

/-- Narrowing beside the wide feature is excluded, which would derive the tripartition grouping
inclusive with second person (60). -/
theorem not_admissible_participant_participantStar :
    ¬ Admissible [.participant, .participantStar] := by decide

/-- Narrowing is not licensed at the top, where the wide feature divides the space. -/
theorem not_admissible_participantStar : ¬ Admissible [.participantStar] := by decide

/-- The admissible hierarchies derive exactly the partitions that Harbour's bivalent geometry (9)
generates, his five (p. 55; [harbour-2016] p. 193). Several hierarchies can derive one partition:
[Author] over the wide [Participant] gives the tripartition, as Figure 4's [Participant] over
[Author] does, since under [+Author] the wide feature makes no contrast. -/
theorem image_graph_sda_eq_geometry :
    ((hierarchies.filter Admissible).map (cellGraph ∘ sda)).toFinset =
      (univ.filter Harbour2016.Admissible).image Harbour2016.graph := by
  decide

end Hammerly2023
