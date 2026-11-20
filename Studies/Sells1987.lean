module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.UpperLower.Principal
public import Linglib.Data.Examples.Sells1987
public import Linglib.Fragments.Ewe.Pronouns
public import Linglib.Fragments.Icelandic.Reciprocals
public import Linglib.Discourse.LogophoricRole
public import Linglib.Data.Examples.Readers

/-!
# Sells (1987): Aspects of Logophoricity

A report has three discourse roles, the source, the self and the pivot, and a discourse
environment says of each whether the external speaker holds it or someone inside the sentence
does, the internal protagonist. We define `Environment.internal e`, the set of roles the
environment `e` gives the protagonist, and show that the four environments are exactly the lower
sets of the hierarchy of roles (`exists_internal_eq_iff`, and `Environment.internalOrderIso` as an
order isomorphism), from which the hierarchy is recovered (`le_iff_forall_mem_internal`).

A role-oriented form takes as antecedent whoever holds its role, so the protagonist can antecede it
exactly where that role is internal. A role `r` fits an observation on some examples,
`Fits obs rows r`, when the observation holds of exactly the examples in whose environment `r` is
internal. The pivot is the one role that fits the binding of Japanese *zibun*
(`fits_zibun_iff`), each of the phrases *that fool*, *mysteriously* and *beloved* is fitted by one
role (`fits_diagnostic_iff`), and the self fits Icelandic *sig*.

## Implementation notes

* An environment records only which roles the protagonist holds. The discourse representation
  structures of the paper are not built, so the difference between a pivot of the matrix clause
  and one of the embedded clause, which the paper uses for strict and sloppy readings, is not
  expressed.
* An example enters with the environment the paper assigns it. An adverbial clause in which the
  speaker takes no one's point of view has no head to specify a role, and is entered with every
  role external.
* `Environment.internal` takes values in `Finset LogophoricRole`, which keeps membership
  decidable, and `Environment.internalOrderEmbedding` bundles it with the proof that each value is a
  lower set.

## TODO

* The claim that role-oriented anaphora is always variable binding.
* The contrast between *came* and *went* under a pivot, and English *own*.
* The subject condition on *sig*, and Italian *proprio*.

## References

* [sells-1987]
-/

@[expose] public section

namespace Sells1987

open Examples (all Environment Diagnostic environment diagnostic reading)

/-! ### Discourse environments -/

namespace Examples.Environment

/-- The environments in the order of Table 1, from direct speech to the logophoric verbs. -/
instance : LinearOrder Environment := LinearOrder.lift' (·.ctorIdx) (by decide)

/-- Table 1: the roles an environment predicates of the internal protagonist, the rest being the
external speaker's. -/
def internal : Environment → Finset LogophoricRole
  | .directSpeech => ∅
  | .thirdPerson => {.pivot}
  | .psychVerb => {.pivot, .self}
  | .logophoricVerb => {.pivot, .self, .source}

variable {e e' : Environment} {r r' : LogophoricRole}

theorem internal_subset_internal : e.internal ⊆ e'.internal ↔ e ≤ e' := by
  revert e e'; decide

end Examples.Environment

open Examples.Environment

variable {e : Environment} {r r' : LogophoricRole}

/-- The table has exactly the role specifications that respect the hierarchy. -/
theorem exists_internal_eq_iff {s : Finset LogophoricRole} :
    (∃ e : Environment, e.internal = s) ↔ IsLowerSet (s : Set LogophoricRole) := by
  have h : ∀ s : Finset LogophoricRole,
      (∃ e : Environment, e.internal = s) ↔ ∀ a ∈ s, ∀ b ≤ a, b ∈ s := by decide
  exact (h s).trans ⟨fun h _ _ hba ha ↦ h _ ha _ hba, fun h _ ha _ hba ↦ h hba ha⟩

namespace Examples.Environment

/-- `Environment.internal` as an order embedding into the lower sets of roles. -/
def internalOrderEmbedding : Environment ↪o LowerSet LogophoricRole :=
  .ofMapLEIff (fun e ↦ ⟨e.internal, exists_internal_eq_iff.1 ⟨e, rfl⟩⟩) fun _ _ ↦
    Finset.coe_subset.trans internal_subset_internal

@[simp]
theorem coe_internalOrderEmbedding (e : Environment) :
    (internalOrderEmbedding e : Set LogophoricRole) = e.internal :=
  rfl

@[simp]
theorem mem_internalOrderEmbedding : r ∈ internalOrderEmbedding e ↔ r ∈ e.internal :=
  Iff.rfl

theorem internalOrderEmbedding_surjective : Function.Surjective internalOrderEmbedding := fun s ↦ by
  classical
  obtain ⟨e, he⟩ := exists_internal_eq_iff (s := (s : Set LogophoricRole).toFinset).2
    (by simp [s.lower])
  exact ⟨e, SetLike.coe_injective (by simp [he])⟩

/-- The environments are the lower sets of the hierarchy of roles, in the order of Table 1. -/
noncomputable def internalOrderIso : Environment ≃o LowerSet LogophoricRole :=
  RelIso.ofSurjective _ internalOrderEmbedding_surjective

@[simp]
theorem coe_internalOrderIso : ⇑internalOrderIso = internalOrderEmbedding :=
  rfl

end Examples.Environment

/-- The hierarchy of roles is the one the table shows, `r` lying below `r'` when `r` is internal
in every environment in which `r'` is. -/
theorem le_iff_forall_mem_internal :
    r ≤ r' ↔ ∀ e : Environment, r' ∈ e.internal → r ∈ e.internal := by
  refine ⟨fun h e ↦ (internalOrderEmbedding e).lower h, fun h ↦ ?_⟩
  obtain ⟨e, he⟩ := internalOrderEmbedding_surjective (.Iic r')
  have h' : r' ∈ internalOrderEmbedding e → r ∈ internalOrderEmbedding e := h e
  rw [he] at h'
  exact h' (LowerSet.mem_Iic_iff.2 le_rfl)

/-! ### The examples -/

/-- A role fits an observation on some examples when each has an environment and the observation
holds of exactly those in whose environment the role is internal. -/
def Fits (obs : Datum → Prop) (rows : List Datum) (r : LogophoricRole) : Prop :=
  ∀ d ∈ rows, ∃ e ∈ environment d, (obs d ↔ r ∈ e.internal)

instance (obs : Datum → Prop) [DecidablePred obs] (rows : List Datum) :
    Decidable (Fits obs rows r) :=
  inferInstanceAs (Decidable (∀ d ∈ rows, ∃ e ∈ environment d, _))

/-- The examples the paper gives of the pronoun `form`. -/
def withPronoun (form : String) : List Datum := all.filter (·.feature? "pronoun" = some form)

/-- The examples the paper gives of the discourse-oriented phrase `k`. -/
def withDiagnostic (k : Diagnostic) : List Datum := all.filter (diagnostic · = some k)

/-- The pronoun of the example has the internal protagonist as antecedent, the indexing the paper
judges. -/
abbrev Bound (d : Datum) : Prop := d.judgment = .acceptable

/-- The discourse-oriented phrase of the example can be understood from the side of the internal
protagonist. -/
abbrev OfProtagonist (d : Datum) : Prop := reading d .internalProtagonist = some .acceptable

/-- The role each discourse-oriented phrase is a diagnostic of. -/
def Examples.Diagnostic.role : Diagnostic → LogophoricRole
  | .thatFool => .source
  | .mysteriously => .self
  | .beloved => .pivot

/-- The pivot is the one role that fits the binding of Japanese *zibun*. The
protagonist binds it under verbs of saying and psychological verbs, negated or not, and in
adverbial clauses reported from the protagonist's point of view, but not in a *when* clause, which
does not invite that point of view. -/
theorem fits_zibun_iff : Fits Bound (withPronoun "zibun") r ↔ r = .pivot := by
  cases r <;> decide

/-- The role a discourse-oriented phrase is a diagnostic of is the one role that fits it: the
source for *that fool*, an evaluation that can be the protagonist's under a verb of saying alone,
the self for *mysteriously*, and the pivot for *beloved*, which goes with the protagonist in all
three environments. -/
theorem fits_diagnostic_iff {k : Diagnostic} :
    Fits OfProtagonist (withDiagnostic k) r ↔ r = k.role := by
  cases k <;> cases r <;> decide

theorem fits_sig : Fits Bound (withPronoun Icelandic.Reciprocals.sig.form) .self := by
  decide

/-- The source does not fit the Ewe logophoric pronoun *yè*, which appears under 'say' and also
under a psychological predicate, where the source is the external speaker's. The paper remarks of
such examples that the self is relevant beside the source, and later suggests the source as the
orientation of logophoric pronouns. -/
theorem fits_ye_iff : Fits Bound (withPronoun Ewe.Pronouns.ye.form) r ↔ r ≠ .source := by
  cases r <;> decide

end Sells1987
