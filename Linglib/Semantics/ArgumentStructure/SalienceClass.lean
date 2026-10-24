module

public import Linglib.Semantics.Root.Kinds
public import Linglib.Semantics.ArgumentStructure.Valency

/-!
# Salience classes

Lucy's classification of verbal roots by required transitiviser —
"salience" is his term for the default semantic values in a root that
influence overt case marking, which is why the classifier lives in the
argument-realization layer. Stated over the (kind signature × arity)
coordinates: agent salient (intransitive manner roots), agent-patient
salient (root transitives), patient salient (intransitive change-of-state
roots). The positional diagnostic (`IsPositional`) is deliberately
separate and arity-free — positional roots cross-cut the transitiviser
classes rather than forming a fourth case.

Originates with Lucy (Yucatec `=t`, `=∅`, `=s`); the Yucatec
instantiation with attested derivations is `Studies/Lucy1994.lean`.

## Main declarations

* `SalienceClass`
* `IsAgentSalient`, `IsPatientSalient`, `IsPositional`
* `SalienceClass.ofKinds` — the pair-level classifier
* `SalienceClass.ofKinds_close` — closure invariance on cause-free
  signatures

## References

* [lucy-1994]
-/

@[expose] public section

namespace ArgumentStructure


/-- Lucy's "three large predicate root classes", named for the
    argument(s) the underived root makes salient. Positional roots are
    deliberately not a case: they fall outside the transitiviser cut
    (`IsPositional`). -/
inductive SalienceClass where
  | agent
  | agentPatient
  | patient
  deriving DecidableEq, Fintype, Repr

variable (s : Root.Kinds) (v : Valency)

/-- Agent salient: intransitive manner-of-action root ("actions or
    activities that some entity undertakes"). -/
abbrev IsAgentSalient : Prop :=
  .internal ∉ v ∧ .manner ∈ s ∧ .result ∉ s

/-- Patient salient: intransitive change-of-state root ("state changes
    that some entity undergoes more or less spontaneously"). -/
abbrev IsPatientSalient : Prop :=
  .internal ∉ v ∧ .manner ∉ s ∧ .result ∈ s

/-- Positional: pure stative configurational signature. Deliberately
    valency-free — a positional root may also zero-derive a transitive
    ([lucy-1994]'s *čin* 'bend'), so the positional class cross-cuts
    the transitiviser cut. -/
abbrev IsPositional : Prop := s = {.state}

/-- The transitiviser cut, over (kind signature × root valency).
    Agent-patient salience is root transitivity (the root introduces
    the internal argument), not a feature configuration; the two
    intransitive classes split by signature; intransitive signatures
    with neither manner nor result — pure statives included — are
    outside the cut. -/
def SalienceClass.ofKinds : Option SalienceClass :=
  if .internal ∈ v then some .agentPatient
  else if IsAgentSalient s v then some .agent
  else if IsPatientSalient s v then some .patient
  else none

/-- Collocational closure does not move the transitiviser cut on
    cause-free signatures: the only available closure edge is
    result→state, which no arm of the classifier consults. -/
theorem SalienceClass.ofKinds_close (h : Root.Kind.cause ∉ s) :
    ofKinds (Root.Kinds.close s) v = ofKinds s v := by
  revert s v; decide

theorem SalienceClass.ofKinds_close_cause :
    ofKinds {.cause} ∅ = none ∧
    ofKinds (Root.Kinds.close {.cause}) ∅ = some .patient := by
  decide

/-! ### Stem valencies -/

/-- The underived stem's valency per salience class: the unergative
    agent stem realizes only Voice's external S, the unaccusative
    patient stem only the internal S, and the root-transitive stem both
    positions. -/
def SalienceClass.stemValency : SalienceClass → Valency
  | .agent => {.external}
  | .agentPatient => {.internal, .external}
  | .patient => {.internal}

theorem SalienceClass.label_stemValency :
    ∀ c : SalienceClass,
      (stemValency c).label =
        if c = .agentPatient then {.A, .P} else {.S} := by decide

end ArgumentStructure
