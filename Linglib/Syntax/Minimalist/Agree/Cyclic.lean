module

public import Linglib.Syntax.Clause.Scenario
public import Linglib.Syntax.Minimalist.Agree.PersonSegment
public import Linglib.Syntax.Minimalist.Probe.Basic
public import Mathlib.Order.Preorder.Chain

/-!
# Cyclic Agree over articulated person probes

Person is decomposed into the privative segments of `Minimalist.PersonSegment`. Every person
bears `π`, speech-act participants also `participant`, and the innermost segments `speaker` and
`addressee` distinguish first from second person according to a geometry, which fixes which
segments a language uses. A probe is a list of unvalued segments. A probe on v first meets the
internal argument and checks every segment it bears; the segments left over, its residue, probe
again from the next projection of v, where the external argument is the closest goal. The context
is direct when the external argument checks some residue, and inverse otherwise, when the core
probe never Agrees with it and its person goes unlicensed. A context is a scenario
(`Clause.Scenario`) of the external over the internal argument, and under a chain geometry it is
direct exactly when it is downstream on the number of probe segments each person bears.

## Main definitions

* `Minimalist.CyclicAgree.PersonGeometry`: the standard, addressee and branching geometries.
* `Minimalist.CyclicAgree.personSpec`: the segments a person bears under a geometry.
* `Minimalist.CyclicAgree.AgreementSystem`: a geometry and an articulated probe, with the residue,
  the direct and inverse contexts, the controller of the agreement slot, person licensing of the
  external argument, and the rank of a person, the number of probe segments it bears.

## Main results

* `Minimalist.CyclicAgree.AgreementSystem.eaLicensed_iff_isDirect`: the core probe licenses the
  external argument exactly in direct contexts.
* `Minimalist.CyclicAgree.AgreementSystem.isDirect_iff_kind_eq_downstream`: under a chain geometry
  a context is direct iff it is downstream on the system's rank.
* `Minimalist.CyclicAgree.AgreementSystem.IsDirect.mono`: a more articulated probe has more direct
  contexts.
* `Minimalist.CyclicAgree.AgreementSystem.flat_isInverse`: a flat probe makes every context
  inverse.

## References

* [bejar-rezac-2009]
* [harley-ritter-2002]
-/

@[expose] public section

namespace Minimalist.CyclicAgree

/-! ### Person geometries -/

/-- A person geometry fixes which innermost segment distinguishes first from second person. It is
`speaker` under `standard` and `addressee` under `addressee`, and under `branching` both are sister
leaves of `participant` ([harley-ritter-2002]). -/
inductive PersonGeometry where
  | standard
  | addressee
  | branching
  deriving DecidableEq, Repr, Fintype

/-- The segments a geometry uses, from the root down. -/
def PersonGeometry.nodes : PersonGeometry → List PersonSegment
  | .standard => [.pi, .participant, .speaker]
  | .addressee => [.pi, .participant, .addressee]
  | .branching => [.pi, .participant, .speaker, .addressee]

/-- The segments a person bears under a geometry, from the root down. -/
def personSpec (geom : PersonGeometry) (p : Person) : List PersonSegment :=
  geom.nodes.filter (· ∈ PersonSegment.spec p)

/-- Every person bears `π` under every geometry. -/
theorem pi_mem_personSpec (geom : PersonGeometry) (p : Person) :
    PersonSegment.pi ∈ personSpec geom p := by
  cases geom <;> simp [personSpec, PersonGeometry.nodes]

/-- A geometry is a chain when the persons' specifications are linearly ordered by inclusion. -/
def PersonGeometry.IsChain (geom : PersonGeometry) : Prop :=
  _root_.IsChain (fun l m : List PersonSegment ↦ l ⊆ m) (Set.range (personSpec geom))

theorem PersonGeometry.standard_isChain : PersonGeometry.standard.IsChain := by
  simp only [PersonGeometry.IsChain, _root_.IsChain, Set.Pairwise, Set.forall_mem_range]
  decide +kernel

theorem PersonGeometry.addressee_isChain : PersonGeometry.addressee.IsChain := by
  simp only [PersonGeometry.IsChain, _root_.IsChain, Set.Pairwise, Set.forall_mem_range]
  decide +kernel

theorem PersonGeometry.not_branching_isChain : ¬ PersonGeometry.branching.IsChain := by
  simp only [PersonGeometry.IsChain, _root_.IsChain, Set.Pairwise, Set.forall_mem_range]
  decide +kernel

/-! ### Articulated probes and agreement systems -/

/-- An articulated probe is a list of unvalued segments, from the most general to the most
specific. -/
abbrev _root_.Minimalist.Probe.Articulation := List PersonSegment

/-- The flat probe `[uπ]`. -/
def flatProbe : Probe.Articulation := [.pi]

/-- The partial probe `[uπ, uparticipant]`, which distinguishes participants from third person. -/
def partialProbe : Probe.Articulation := [.pi, .participant]

/-- The full probe of a geometry, every segment the geometry uses. -/
def fullProbe (geom : PersonGeometry) : Probe.Articulation := geom.nodes

/-- A language's agreement system is a person geometry together with an articulated probe. -/
structure AgreementSystem where
  /-- The person geometry. -/
  geometry : PersonGeometry
  /-- The articulated probe. -/
  probe : Probe.Articulation
  deriving DecidableEq, Repr

/-- One of the two arguments of a transitive clause. -/
inductive Argument where
  | ia
  | ea
  deriving DecidableEq, Repr

namespace AgreementSystem

open Clause (Scenario)

variable (sys : AgreementSystem) (s : Scenario Person)

/-- The segments a person bears under the system's geometry. -/
abbrev spec (p : Person) : List PersonSegment := personSpec sys.geometry p

/-- The residue of the probe after Agree with the internal argument, the segments it does not
bear. -/
def residue (ia : Person) : Probe.Articulation := sys.probe.filter fun x ↦ decide (x ∉ sys.spec ia)

/-- A context, the scenario of the external over the internal argument, is direct when the
external argument bears some segment of the residue. -/
def IsDirect : Prop := ∃ x ∈ sys.residue s.low, x ∈ sys.spec s.high

/-- A context is inverse when it is not direct. -/
def IsInverse : Prop := ¬ sys.IsDirect s

instance : DecidablePred sys.IsDirect := fun _ ↦ List.decidableBEx _ _

instance : DecidablePred sys.IsInverse := fun _ ↦ instDecidableNot

theorem isDirect_iff :
    sys.IsDirect s ↔ ∃ x ∈ sys.probe, x ∉ sys.spec s.low ∧ x ∈ sys.spec s.high := by
  simp only [IsDirect, residue, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun ⟨x, ⟨h1, h2⟩, h3⟩ ↦ ⟨x, h1, h2, h3⟩, fun ⟨x, h1, h2, h3⟩ ↦ ⟨x, ⟨h1, h2⟩, h3⟩⟩

/-- The argument controlling the agreement slot, the external argument in a direct context. -/
def controller : Argument := if sys.IsDirect s then .ea else .ia

/-- The person the agreement slot realizes. -/
def value : Person := if sys.IsDirect s then s.high else s.low

/-- The segments checked on each cycle, by the internal argument and then by the external one
out of the residue. -/
def cycles : Probe.Articulation × Probe.Articulation :=
  (sys.probe.filter (· ∈ sys.spec s.low), (sys.residue s.low).filter (· ∈ sys.spec s.high))

/-- The rank of a person on the system's scale is the number of probe segments it bears. -/
def rank (p : Person) : ℕ := (sys.probe.filter (· ∈ sys.spec p)).length

/-- A segment of the probe searches its domain, halting at the closest goal, which bears `π` and
so intervenes for every segment, and Agrees with that goal iff it bears the segment. -/
def segProbe (s : PersonSegment) : Probe Person := .ofInt fun p ↦ decide (s ∈ sys.spec p)

/-- The external argument is licensed by the core probe when some segment of the residue Agrees
with it from the next projection of v, whose domain has the external argument closest and the
internal one below. -/
def EALicensed : Prop :=
  ∃ x ∈ sys.residue s.low, (sys.segProbe x).goal [s.high, s.low] = some s.high

instance : DecidablePred sys.EALicensed := fun _ ↦ List.decidableBEx _ _

/-- The core probe licenses the external argument exactly in direct contexts. -/
theorem eaLicensed_iff_isDirect : sys.EALicensed s ↔ sys.IsDirect s := by
  simp only [EALicensed, IsDirect, segProbe, Probe.ofInt_goal_eq_some_iff, List.head?_cons,
    true_and, decide_eq_true_eq]

/-- Arguments of the same person make an inverse context. -/
theorem isInverse_self (p : Person) : sys.IsInverse ⟨p, p⟩ := fun h ↦
  let ⟨_, _, hn, hm⟩ := (sys.isDirect_iff ⟨p, p⟩).1 h
  hn hm

/-- A probe with more segments has more direct contexts. -/
theorem IsDirect.mono {sys' : AgreementSystem} (hg : sys'.geometry = sys.geometry)
    (hp : sys.probe ⊆ sys'.probe) (h : sys.IsDirect s) : sys'.IsDirect s := by
  rw [isDirect_iff] at h ⊢
  obtain ⟨x, hx, h⟩ := h
  exact ⟨x, hp hx, by simpa [spec, hg] using h⟩

/-- A flat probe leaves no residue, since every internal argument bears `π`, so every context is
inverse. -/
theorem flat_isInverse (geom : PersonGeometry) :
    (⟨geom, flatProbe⟩ : AgreementSystem).IsInverse s := by
  rintro ⟨x, hx, -⟩
  simp [residue, flatProbe, spec, pi_mem_personSpec] at hx

theorem spec_subset_or_subset {geom : PersonGeometry} (h : geom.IsChain) (p q : Person) :
    personSpec geom p ⊆ personSpec geom q ∨ personSpec geom q ⊆ personSpec geom p := by
  by_cases hpq : personSpec geom p = personSpec geom q
  · exact Or.inl (hpq ▸ List.Subset.refl _)
  · exact h (Set.mem_range_self p) (Set.mem_range_self q) hpq

/-- Under a chain geometry a context is direct iff the external argument bears more of the
probe than the internal one does. -/
theorem isDirect_iff_rank_lt (h : sys.geometry.IsChain) :
    sys.IsDirect s ↔ sys.rank s.low < sys.rank s.high := by
  rcases spec_subset_or_subset h s.low s.high with hsub | hsub
  · have key : sys.probe.filter (· ∈ sys.spec s.low) =
        (sys.probe.filter (· ∈ sys.spec s.high)).filter (· ∈ sys.spec s.low) := by
      rw [List.filter_filter]
      exact List.filter_congr fun x _ ↦ by
        by_cases hi : x ∈ sys.spec s.low
        · simp [hi, hsub hi]
        · simp [hi]
    rw [rank, rank, key, List.length_filter_lt_length_iff_exists, isDirect_iff]
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun ⟨x, hx, hi, he⟩ ↦ ⟨x, ⟨hx, he⟩, hi⟩, fun ⟨x, ⟨hx, he⟩, hi⟩ ↦ ⟨x, hx, hi, he⟩⟩
  · constructor
    · intro h
      obtain ⟨x, _, hn, hm⟩ := (sys.isDirect_iff s).1 h
      exact absurd (hsub hm) hn
    · intro hlt
      have := List.countP_mono_left (l := sys.probe) (p := fun x ↦ decide (x ∈ sys.spec s.high))
        (q := fun x ↦ decide (x ∈ sys.spec s.low)) fun x _ h ↦ by
          simpa using hsub (by simpa using h)
      simp only [List.countP_eq_length_filter] at this
      exact absurd this (not_le.2 hlt)

/-- Under a chain geometry a context is direct iff it is downstream on the system's rank, so the
inverse contexts are the balanced and upstream scenarios. -/
theorem isDirect_iff_kind_eq_downstream (h : sys.geometry.IsChain) :
    sys.IsDirect s ↔ (s.map sys.rank).kind = .downstream :=
  (sys.isDirect_iff_rank_lt s h).trans (Scenario.kind_eq_downstream_iff (s := s.map sys.rank)).symm

end AgreementSystem

end Minimalist.CyclicAgree
