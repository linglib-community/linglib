module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Root content

What a root says about the action, its result, and the patient, the fine,
within-class half of a root's meaning; the coarse half, which templatic
components it entails, is `Root.Kinds`. Each dimension is a region of a finite
scale rather than a point, since a verb is compatible with a range of force
levels, patient materials, or result geometries. Spalek and McNally separate
English *tear* from Spanish *rasgar*, two roots of one kind, by patient
robustness, force direction, and compatibility with careful action;
Majid, Boster and Bowerman vary the instrument and the object's rigidity and
dimensionality across their cutting and breaking events. A described situation,
`Root.Content.Situation`, is a point of the product of the dimensions, and a
`Root.Content` is a box in that space, one region per dimension, `univ` where a root
says nothing; two contents overlap when the boxes meet, which is when some situation
lies in both (`Root.Content.overlaps_iff_exists_mem`).

## Main declarations

* `Root.Content.ForceLevel`, `ForceDirection`, `InstrumentType`, `AgentControl` —
  dimensions of the action; `ResultGeometry` of the result; `Robustness`,
  `ObjectDimensionality` of the patient
* `Root.Content.Situation` — a value on every dimension
* `Root.Content` — a region per dimension, containing situations
* `Root.Content.Overlaps` — the regions meet on every dimension

## References

* [spalek-mcnally-2026]: The anatomy of a verb.
* [majid-boster-bowerman-2008]: The cross-linguistic categorization of everyday
  events.
* [talmy-1988]: Force dynamics in language and cognition.
* [levin-1993]: English Verb Classes and Alternations.
-/

@[expose] public section

namespace Semantics.Root.Content

/-! ### Dimensions -/

/-- Magnitude of the force involved ([talmy-1988]). -/
inductive ForceLevel where
  /-- No force component, as in states. -/
  | zero
  | low
  | moderate
  | high
  deriving DecidableEq, Fintype, Repr

/-- Spatial pattern of the force applied ([talmy-2000]), contrary directions for
*tear* and a single direction for *rasgar* ([spalek-mcnally-2026]). -/
inductive ForceDirection where
  | undirected
  | unidirectional
  | bidirectional
  | omnidirectional
  deriving DecidableEq, Fintype, Repr

/-- Material substantiality of the patient, on which *rasgar* is restricted to
flimsy patients and *tear* is not ([spalek-mcnally-2026]). -/
inductive Robustness where
  | insubstantial
  | flimsy
  | moderate
  | robust
  deriving DecidableEq, Fintype, Repr

/-- The physical change produced, after the class descriptions of [levin-1993]
(§45.1 break, §45.2 bend, §44 destroy, §21.1 cut) and [hale-keyser-1987]'s
separation in material integrity. -/
inductive ResultGeometry where
  /-- Loss of integrity by pulling apart (*tear*). -/
  | separation
  /-- Damage to a surface (*rasgar*, *cut*). -/
  | surfaceBreach
  /-- Breakage along stress lines (*crack*, *break*). -/
  | fracture
  /-- Complete structural failure (*shatter*, *smash*). -/
  | fragmentation
  /-- Change of shape with integrity preserved (*bend*, *fold*). -/
  | deformation
  /-- The entity ceases to exist as such (*destroy*). -/
  | totalDestruction
  deriving DecidableEq, Fintype, Repr

/-- The instrument effecting a separation, which together with the object and the
manner of action determines how predictable the locus of separation is
([majid-boster-bowerman-2008]). -/
inductive InstrumentType where
  | sharpBlade
  | bluntImpact
  | hands
  | other
  deriving DecidableEq, Fintype, Repr

/-- Dimensionality of the patient, the twig that snaps, the cloth that tears, or the
pot that smashes ([majid-boster-bowerman-2008]). -/
inductive ObjectDimensionality where
  | oneD
  | twoD
  | threeD
  deriving DecidableEq, Fintype, Repr

/-- Compatibility with careful, controlled action, which *tear* has and *rasgar*
lacks ([spalek-mcnally-2026]). -/
inductive AgentControl where
  | incompatible
  | neutral
  | compatible
  deriving DecidableEq, Fintype, Repr

/-- A described situation, a point of the content space: a value on every dimension. -/
structure Situation where
  force : ForceLevel
  forceDirection : ForceDirection
  instrument : InstrumentType
  agentControl : AgentControl
  resultGeometry : ResultGeometry
  patientRobustness : Robustness
  patientDimensionality : ObjectDimensionality
  deriving DecidableEq, Repr

end Semantics.Root.Content

namespace Semantics.Root

open Content Finset

/-- A root's content, a region of each dimension, `univ` where the root says nothing. -/
structure Content where
  /-- Magnitude of the force applied. -/
  force : Finset ForceLevel := univ
  /-- Direction of the force applied. -/
  forceDirection : Finset ForceDirection := univ
  /-- The instrument selected for. -/
  instrument : Finset InstrumentType := univ
  /-- Compatibility with careful action. -/
  agentControl : Finset AgentControl := univ
  /-- The physical change produced. -/
  resultGeometry : Finset ResultGeometry := univ
  /-- Robustness of the patient. -/
  patientRobustness : Finset Robustness := univ
  /-- Dimensionality of the patient. -/
  patientDimensionality : Finset ObjectDimensionality := univ
  deriving DecidableEq

namespace Content

variable {p q c : Content} {s : Situation}

/-- A content contains a situation when each of its regions contains the situation's value on
that dimension, so a content is a box in the space of situations. -/
instance : Membership Situation Content where
  mem c s := s.force ∈ c.force ∧ s.forceDirection ∈ c.forceDirection ∧
    s.instrument ∈ c.instrument ∧ s.agentControl ∈ c.agentControl ∧
    s.resultGeometry ∈ c.resultGeometry ∧ s.patientRobustness ∈ c.patientRobustness ∧
    s.patientDimensionality ∈ c.patientDimensionality

theorem mem_iff : s ∈ c ↔ s.force ∈ c.force ∧ s.forceDirection ∈ c.forceDirection ∧
    s.instrument ∈ c.instrument ∧ s.agentControl ∈ c.agentControl ∧
    s.resultGeometry ∈ c.resultGeometry ∧ s.patientRobustness ∈ c.patientRobustness ∧
    s.patientDimensionality ∈ c.patientDimensionality := Iff.rfl

instance (c : Content) (s : Situation) : Decidable (s ∈ c) := decidable_of_iff _ mem_iff.symm

/-- Two contents overlap when their regions meet on every dimension. -/
def Overlaps (p q : Content) : Prop :=
  ¬ Disjoint p.force q.force ∧ ¬ Disjoint p.forceDirection q.forceDirection ∧
    ¬ Disjoint p.instrument q.instrument ∧ ¬ Disjoint p.agentControl q.agentControl ∧
    ¬ Disjoint p.resultGeometry q.resultGeometry ∧
    ¬ Disjoint p.patientRobustness q.patientRobustness ∧
    ¬ Disjoint p.patientDimensionality q.patientDimensionality

instance (p q : Content) : Decidable (p.Overlaps q) := by unfold Overlaps; infer_instance

theorem overlaps_iff_exists_mem : p.Overlaps q ↔ ∃ s, s ∈ p ∧ s ∈ q := by
  simp only [Overlaps, mem_iff, Finset.not_disjoint_iff]
  constructor
  · rintro ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩, ⟨c, hc, hc'⟩, ⟨d, hd, hd'⟩, ⟨e, he, he'⟩,
      ⟨f, hf, hf'⟩, ⟨g, hg, hg'⟩⟩
    exact ⟨⟨a, b, c, d, e, f, g⟩, ⟨ha, hb, hc, hd, he, hf, hg⟩, ha', hb', hc', hd', he', hf', hg'⟩
  · rintro ⟨s, ⟨ha, hb, hc, hd, he, hf, hg⟩, ha', hb', hc', hd', he', hf', hg'⟩
    exact ⟨⟨_, ha, ha'⟩, ⟨_, hb, hb'⟩, ⟨_, hc, hc'⟩, ⟨_, hd, hd'⟩, ⟨_, he, he'⟩, ⟨_, hf, hf'⟩,
      ⟨_, hg, hg'⟩⟩

end Content

end Semantics.Root
