/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Composition.Mode
public import Linglib.Semantics.Presupposition.PhiFeatures
public import Studies.Landau2013
public import Studies.Landau2015
public import Linglib.Data.Examples.Landau2024a

/-!
# Landau (2024): Control

Landau's Element surveys control theory. This file states its generalizations over the examples
it gives, each derived from the library's account of the phenomenon.

Obligatory control is Landau's earlier signature, read off the rows. Non-obligatory control is
the non-OC behaviour of a clause that shows obligatory control somewhere, and no control the
behaviour of a clause that never does; this sorts the Spanish paradigm (41) (`status_41`). The
revised Visser's generalization (19) holds of the Norwegian passives (20) but fails for implicit
control into an interrogative (22a), the exception the Element leaves a puzzle (`not_rvg`).

On the embedded-speech-act theory, the subject of a jussive bears a person feature, and under a
verb of saying it is evaluated at the reported context, whose agent and addressee are the matrix
subject and object. The associative person semantics then gives a first person exclusive subject
subject control, a second person one object control and an inclusive one split control
(`mem_participantSets_reported`), Postal's correlation (33), which the Korean jussive markers
realize (35) (`jussive_rows`).

Partial control is available exactly under the verbs whose derived tier is logophoric
(`partialControl_rows`). A lexical subject saturates the property a predicative complement
denotes, so only a propositional complement hosts one (72) (`lexicalSubject_iff_logophoric`), and
the same cut separates strict from alternating adjunct control (89)
(`hasPropositionalVariant_iff_admitsNOC`, `adjunct_rows`). Non-obligatory control is licensed by a
topic or by a logophoric center, and the paradigm (52) shows that neither is necessary
(`noc_rows`).

## Implementation notes

The rows are read as diagnostics by `Landau2013.attests`; a clause in a position shows obligatory
control when its rows attest none. The tiers and their availability of partial control are those
of `Studies/Landau2015.lean`, and a row's verb is the English fragment's entry. The persons of the
jussives are the orientations the Element gives them in matrix clauses. The rows of (35) follow
the translations and the prose, where the page's index on PRO in (35b) disagrees. An adjunct's
head selects the complements of some tiers; the strict adjuncts of (84a) select predicative ones
only.

## References

* [landau-2024a]
* [landau-2013]
* [landau-2015]
* [van-urk-2013]
* [postal-1970]
* [grano-2015]
-/

@[expose] public section

namespace Landau2024a

open Control Landau2015 Montague

/-! ### The trichotomy (41) -/

/-- The clause types of the Spanish paradigm (41). -/
inductive ClauseType where
  | infinitive
  | finite
  deriving DecidableEq, Repr

/-- The positions of the Spanish paradigm (41). -/
inductive Position where
  | complement
  | subject
  deriving DecidableEq, Repr, Fintype

/-- The clause type of a row. -/
def clauseTypeOf (row : Datum) : Option ClauseType :=
  row.parse? "clause" [("infinitive", .infinitive), ("finite", .finite)]

/-- The position of a row's clause. -/
def positionOf (row : Datum) : Option Position :=
  row.parse? "position" [("complement", .complement), ("subject", .subject)]

/-- The diagnostics the rows attest for a clause type in a position. -/
def attested (c : ClauseType) (p : Position) : Set Diagnostic :=
  {d | ∃ row ∈ Examples.all, clauseTypeOf row = some c ∧ positionOf row = some p ∧
    Landau2013.attests row d}

instance (c : ClauseType) (p : Position) : DecidablePred (· ∈ attested c p) := fun d ↦ by
  unfold attested; infer_instance

/-- A clause type in a position shows obligatory control when every clause of the signature
holds, no row attesting a diagnostic. -/
def IsOC (c : ClauseType) (p : Position) : Prop :=
  ofAttested (ι := Landau2013.Clause74) (attested c p) = Set.univ

instance (c : ClauseType) (p : Position) : Decidable (IsOC c p) :=
  decidable_of_iff (∀ d, d ∉ attested c p) <| by
    rw [IsOC, ofAttested_eq_univ_iff, Set.eq_empty_iff_forall_notMem]

/-- The control statuses, obligatory, non-obligatory and no control. -/
inductive Status where
  | oc
  | noc
  | nc
  deriving DecidableEq, Repr

/-- The status of a clause type in a position. A clause shows obligatory control where the
signature holds; otherwise its behaviour is non-obligatory control if it shows obligatory control
in some position, and no control if it never does. -/
def Status.of (c : ClauseType) (p : Position) : Status :=
  if IsOC c p then .oc else if ∃ q, IsOC c q then .noc else .nc

/-- In the Spanish paradigm (41), infinitives show obligatory control as complements and
non-obligatory control as subjects, and finite clauses no control in either position. -/
theorem status_41 :
    Status.of .infinitive .complement = .oc ∧ Status.of .infinitive .subject = .noc ∧
      Status.of .finite .complement = .nc ∧ Status.of .finite .subject = .nc := by
  decide +kernel

theorem exists_oc_of_noc {c : ClauseType} {p : Position} (h : Status.of c p = .noc) :
    ∃ q, Status.of c q = .oc := by
  unfold Status.of at h
  split_ifs at h with h₁ h₂
  obtain ⟨q, hq⟩ := h₂
  exact ⟨q, by simp [Status.of, hq]⟩

/-! ### The revised Visser's generalization (19), (20), (22) -/

/-- The revised Visser's generalization (19) holds of a row when an implicit controller under T
agreeing with a referential DP makes it ungrammatical. -/
def RVG (row : Datum) : Prop :=
  row.feature? "controller" = some "implicit" → row.feature? "tAgrees" = some "referential" →
    row.judgment = .ungrammatical

instance (row : Datum) : Decidable (RVG row) := inferInstanceAs (Decidable (_ → _ → _))

/-- The Norwegian passives of *promise* (20) obey the generalization: the personal passive, with
T agreeing with the promisee, bars implicit control, and the impersonal one allows it. -/
theorem rvg_20 :
    RVG Examples.ex_20a ∧ RVG Examples.ex_20b ∧ Examples.ex_20b.judgment = .acceptable := by
  decide

/-- Implicit control into an interrogative complement under a personal passive (22a) is a
genuine exception, so the generalization does not hold of the rows. -/
theorem not_rvg : ¬ ∀ row ∈ Examples.all, RVG row := by
  decide +kernel

/-! ### The direct-discourse correlation (33) and the Korean jussives (35) -/

/-- The Korean jussive markers of (35), volitional *keyss*, imperative *la* and exhortative
*ca*. -/
inductive Jussive where
  | volitional
  | imperative
  | exhortative
  deriving DecidableEq, Repr

/-- The person of a jussive's subject is its orientation in matrix clauses. The volitional is
speaker-oriented, the imperative addressee-oriented, and the exhortative oriented to the speaker
and the addressee. -/
def Jussive.person : Jussive → Person
  | .volitional => .firstExclusive
  | .imperative => .second
  | .exhortative => .firstInclusive

/-- The jussive of a row's embedded clause, `none` for the indicative. -/
def jussiveOf (row : Datum) : Option Jussive :=
  row.parse? "mood" [("volitional", .volitional), ("imperative", .imperative),
    ("exhortative", .exhortative)]

section Reported

variable {W E P T : Type*} [PartialOrder E] (c : Kaplan.Context W E P T) (s o x : E)

/-- The context a verb of saying reports, whose agent is the matrix subject `s` and whose
addressee is the matrix object `o`. -/
def reported : Kaplan.Context W E P T := { c with agent := s, addressee := o }

/-- Evaluated at the reported context, a first person exclusive subject includes the matrix
subject and not the object, a second person one the object and not the subject, and an inclusive
one both: subject, object and split control. The first two are Postal's correlation (33). -/
theorem mem_participantSets_reported :
    ((reported c s o).participants x ∈ Person.firstExclusive.participantSets ↔
        s ≤ x ∧ ¬ o ≤ x) ∧
      ((reported c s o).participants x ∈ Person.second.participantSets ↔ o ≤ x ∧ ¬ s ≤ x) ∧
      ((reported c s o).participants x ∈ Person.firstInclusive.participantSets ↔
        s ≤ x ∧ o ≤ x) := by
  simp only [Person.participantSets, Finset.mem_singleton, Finset.ext_iff,
    Discourse.Role.forall_role, Kaplan.Context.speaker_mem_participants,
    Kaplan.Context.addressee_mem_participants, reported]
  simp; tauto

end Reported

/-- The roles of the reported context that a controlled reading's subject includes, the agent for
subject control, the addressee for object control, both for split control, and neither for a free
reading. -/
def roles : String → Option (Finset Discourse.Role)
  | "subject" => some {.speaker}
  | "object" => some {.addressee}
  | "split" => some {.speaker, .addressee}
  | "free" => some ∅
  | _ => none

/-- Under *mal* 'say', a jussive's controlled readings are exactly those whose roles form a cell
of its person (35b)–(35d), and the indicative controls nothing (35a). -/
theorem jussive_rows :
    ∀ row ∈ Examples.all, row.feature? "verb" = some "mal" → ∀ r ∈ row.readings,
      ∀ rs ∈ roles r.1, (r.2 = .acceptable ↔
        ∀ j ∈ jussiveOf row, rs ∈ j.person.participantSets) := by
  decide +kernel

/-! ### Partial control (36), (37) -/

/-- The English fragment's entry for a row's verb. -/
def verbOf (row : Datum) : Option Verb :=
  (row.feature? "verb").bind (Verb.find? (English.Verbs.verbs.map (·.toVerb)) ·)

/-- Partial control is acceptable exactly under the verbs whose derived class lies on a tier
admitting it: the attitude predicates of (36), not the implicative of (37a). -/
theorem partialControl_rows :
    ∀ row ∈ Examples.all, ∀ v ∈ verbOf row, row.feature? "reading" = some "partial" →
      (row.judgment = .acceptable ↔
        ∃ cls, derivedLandauClass v = some cls ∧ Table80Row.partialControl.Available cls.tier) := by
  simp only [available_iff_logophoric (r := .partialControl) (by simp)]
  decide +kernel

/-! ### Lexical subjects (72) -/

/-- The type of a tier's complement. A FinP is a property, a λ-abstract over PRO; a predicative
complement is the FinP itself, and a logophoric one the FinP applied to the projected *pro*. -/
def complementTy : Tier → Option Ty
  | .predicative => some .et
  | .logophoric => Ty.combine? .e .et

/-- A lexical subject saturates the FinP, so a clause hosting one has the type of the FinP applied
to an individual, which only a logophoric complement has (72). -/
theorem lexicalSubject_iff_logophoric (t : Tier) :
    complementTy t = Ty.combine? .e .et ↔ t = .logophoric := by
  cases t <;> decide

/-! ### Adjunct control (84), (89) -/

/-- The English controlled adjuncts of (84). -/
inductive AdjunctType where
  | goal
  | result
  | stimulus
  | subjectPurpose
  | objectPurpose
  | rationale
  | temporal
  | absolutive
  | justification
  | telic
  deriving DecidableEq, Repr

/-- The tiers whose complements an adjunct's head selects (89), predicative ones for every
adjunct and logophoric ones as well for the alternating adjuncts of (84b). -/
def AdjunctType.tiers : AdjunctType → Finset Tier
  | .goal | .result | .stimulus | .subjectPurpose => {.predicative}
  | _ => {.predicative, .logophoric}

/-- An adjunct admits non-obligatory control when its head selects a logophoric clause, whose
controller is identified by logophoric antecedence rather than predication. -/
def AdjunctType.AdmitsNOC (a : AdjunctType) : Prop := .logophoric ∈ a.tiers

/-- An adjunct has a propositional variant when its head selects a clause hosting a lexical
subject, of the type of a FinP applied to an individual. -/
def AdjunctType.HasPropositionalVariant (a : AdjunctType) : Prop :=
  ∃ t ∈ a.tiers, complementTy t = Ty.combine? .e .et

instance : DecidablePred AdjunctType.AdmitsNOC := fun a ↦
  inferInstanceAs (Decidable (Tier.logophoric ∈ a.tiers))

instance : DecidablePred AdjunctType.HasPropositionalVariant := fun a ↦
  inferInstanceAs (Decidable (∃ t ∈ a.tiers, _))

/-- By the propositional-variant criterion (89), an adjunct alternates into non-obligatory control
exactly when it has a propositional variant. -/
theorem hasPropositionalVariant_iff_admitsNOC (a : AdjunctType) :
    a.HasPropositionalVariant ↔ a.AdmitsNOC := by
  simp [AdjunctType.HasPropositionalVariant, AdjunctType.AdmitsNOC, lexicalSubject_iff_logophoric]

/-- The adjunct type of a row. -/
def adjunctOf (row : Datum) : Option AdjunctType :=
  row.parse? "adjunct" [("stimulus", .stimulus), ("justification", .justification)]

/-- The rows bear the criterion out (87), (88): a stimulus clause hosts no lexical subject and
rejects non-c-commanding control, and a justification clause does both. -/
theorem adjunct_rows : ∀ row ∈ Examples.all, ∀ a ∈ adjunctOf row,
    (row.feature? "subject" = some "lexical" →
      (row.judgment = .acceptable ↔ a.HasPropositionalVariant)) ∧
    (row.feature? "antecedent" = some "nonCCommanding" →
      (Landau2013.attests row .nonCCommandingControl ↔ a.AdmitsNOC)) := by
  decide +kernel

/-! ### Non-obligatory control: topic and logophoric center (52), (55) -/

/-- The controller of a row is a topic. -/
def IsTopic (row : Datum) : Prop := row.feature? "topic" = some "+"

/-- The controller of a row is a logophoric center. -/
def IsLogophoric (row : Datum) : Prop := row.feature? "logophoric" = some "+"

instance (row : Datum) : Decidable (IsTopic row) := inferInstanceAs (Decidable (_ = _))

instance (row : Datum) : Decidable (IsLogophoric row) := inferInstanceAs (Decidable (_ = _))

/-- On the paradigm (52), the pragmatics of NOC (55a) holds: every acceptable controller is a
topic or a logophoric center, and each licensor occurs without the other, so neither is
necessary. -/
theorem noc_rows :
    (∀ row ∈ Examples.all, row.feature? "control" = some "NOC" → row.judgment = .acceptable →
      IsTopic row ∨ IsLogophoric row) ∧
    (∃ row ∈ Examples.all, row.feature? "control" = some "NOC" ∧
      row.judgment = .acceptable ∧ ¬ IsTopic row) ∧
    (∃ row ∈ Examples.all, row.feature? "control" = some "NOC" ∧
      row.judgment = .acceptable ∧ ¬ IsLogophoric row) := by
  decide +kernel

end Landau2024a
