module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Defs.Unbundled
public import Linglib.Data.Examples.Sells1987
public import Linglib.Fragments.Ewe.Pronouns
public import Linglib.Fragments.Icelandic.Reciprocals
public import Linglib.Semantics.Reference.Logophoricity

/-!
# Sells (1987): Aspects of Logophoricity

Sells takes logophoricity apart into three discourse roles, the source, the self and the pivot.
A discourse environment says of each role whether the external speaker holds it or someone inside
the sentence does, the internal protagonist. A role-oriented form takes as antecedent whoever
holds its role, so the protagonist can antecede it exactly where that role is internal: Japanese
*zibun* is oriented to the pivot, Icelandic *sig* to the self, and the phrases *that fool*,
*mysteriously* and *beloved* to the source, the self and the pivot.

## Main statements

* `le_iff_forall_mem_internal`: the hierarchy of roles is the one the table of environments
  shows, a role lying below another when it is internal wherever the other is.
* `exists_internal_eq_iff`: the table has exactly the specifications that respect the hierarchy,
  four of the eight.
* `fits_zibun_iff`, `fits_thatFool_iff`, `fits_mysteriously_iff`, `fits_beloved_iff`: over the
  paper's examples the role of each form is the only one that is internal in just the environments
  where the form goes with the protagonist.
* `fits_ye_iff`: the source, which the paper suggests for logophoric pronouns, does not fit its
  Ewe example with a psychological predicate.

## Implementation notes

* An environment records only which roles the protagonist holds. The discourse representation
  structures of the paper are not built, so the difference between a pivot of the matrix clause
  and one of the embedded clause, which the paper uses for strict and sloppy readings, is not
  expressed.
* An example enters with the environment the paper assigns it. An adverbial clause in which the
  speaker takes no one's point of view has no head to specify a role, and is entered with every
  role external.

## TODO

* The claim that role-oriented anaphora is always variable binding.
* The contrast between *came* and *went* under a pivot, and English *own*.
* The subject condition on *sig*, and Italian *proprio*.

## References

* [sells-1987]
-/

@[expose] public section

namespace Sells1987

/-! ### Discourse environments -/

/-- The discourse environments of the paper's first table. -/
inductive Environment where
  /-- Direct speech, in which the external speaker holds every role. -/
  | directSpeech
  /-- Third-person point of view, in which the speaker reports from where someone in the sentence
  stands. It arises by construction, as in an adverbial clause, and not from a predicate. -/
  | thirdPerson
  /-- The complement of a psychological verb such as *distress*, through which the speaker reports
  the state of mind of someone in the sentence. -/
  | psychVerb
  /-- The complement of a verb of communication such as *say*, the fully logophoric case. -/
  | logophoricVerb
  deriving DecidableEq, Fintype, Repr

/-- The roles an environment predicates of the internal protagonist, the rest being the external
speaker's. -/
def Environment.internal : Environment → Finset LogophoricRole
  | .directSpeech => ∅
  | .thirdPerson => {.pivot}
  | .psychVerb => {.pivot, .self}
  | .logophoricVerb => {.pivot, .self, .source}

variable {e : Environment} {r r' : LogophoricRole}

theorem le_iff_forall_mem_internal :
    r ≤ r' ↔ ∀ e : Environment, r' ∈ e.internal → r ∈ e.internal := by
  cases r <;> cases r' <;> decide

theorem exists_internal_eq_iff {s : Finset LogophoricRole} :
    (∃ e : Environment, e.internal = s) ↔ IsLowerSet (s : Set LogophoricRole) := by
  have h : ∀ s : Finset LogophoricRole,
      (∃ e : Environment, e.internal = s) ↔ ∀ a ∈ s, ∀ b ≤ a, b ∈ s := by decide
  exact (h s).trans ⟨fun h _ _ hba ha ↦ h _ ha _ hba, fun h _ ha _ hba ↦ h hba ha⟩

theorem Environment.pivot_mem_internal_iff : .pivot ∈ e.internal ↔ e ≠ .directSpeech := by
  cases e <;> decide

theorem Environment.self_mem_internal_iff :
    .self ∈ e.internal ↔ e = .psychVerb ∨ e = .logophoricVerb := by
  cases e <;> decide

theorem Environment.source_mem_internal_iff : .source ∈ e.internal ↔ e = .logophoricVerb := by
  cases e <;> decide

/-! ### The examples -/

/-- The environment the paper assigns an example. -/
def environment? (d : Datum) : Option Environment :=
  d.parse? "environment"
    [("logophoric verb", .logophoricVerb), ("psych-verb", .psychVerb), ("3POV", .thirdPerson),
      ("external", .directSpeech)]

/-- The examples the paper gives of the pronoun or the discourse-oriented phrase `value`. -/
def examplesOf (key value : String) : List Datum :=
  Examples.all.filter (·.feature? key = some value)

/-- A role fits an observation on some examples when each has an environment and the observation
holds of exactly those in whose environment the role is internal. -/
def Fits (obs : Datum → Prop) (rows : List Datum) (r : LogophoricRole) : Prop :=
  ∀ d ∈ rows, ∃ e ∈ environment? d, (obs d ↔ r ∈ e.internal)

instance (obs : Datum → Prop) [DecidablePred obs] (rows : List Datum) :
    Decidable (Fits obs rows r) :=
  inferInstanceAs (Decidable (∀ d ∈ rows, ∃ e ∈ environment? d, _))

/-- The pronoun of the example has the internal protagonist as antecedent, the indexing the paper
judges. -/
abbrev Bound (d : Datum) : Prop := d.judgment = .acceptable

/-- The discourse-oriented phrase of the example can be understood from the side of the internal
protagonist. -/
def OfProtagonist (d : Datum) : Prop := ("internal protagonist", Judgment.acceptable) ∈ d.readings

instance : DecidablePred OfProtagonist := fun _ ↦ inferInstanceAs (Decidable (_ ∈ _))

theorem fits_zibun_iff : Fits Bound (examplesOf "pronoun" "zibun") r ↔ r = .pivot := by
  cases r <;> decide

theorem fits_thatFool_iff :
    Fits OfProtagonist (examplesOf "diagnostic" "that fool") r ↔ r = .source := by
  cases r <;> decide

theorem fits_mysteriously_iff :
    Fits OfProtagonist (examplesOf "diagnostic" "mysteriously") r ↔ r = .self := by
  cases r <;> decide

theorem fits_beloved_iff :
    Fits OfProtagonist (examplesOf "diagnostic" "beloved") r ↔ r = .pivot := by
  cases r <;> decide

theorem fits_sig : Fits Bound (examplesOf "pronoun" Icelandic.Reciprocals.sig.form) .self := by
  decide

theorem fits_ye_iff : Fits Bound (examplesOf "pronoun" Ewe.Pronouns.ye.form) r ↔ r ≠ .source := by
  cases r <;> decide

end Sells1987
