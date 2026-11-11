module

public import Linglib.Syntax.Agreement.PersonSegment
public import Linglib.Syntax.Clause.Scenario
public import Linglib.Syntax.Minimalist.Probe.Agree

/-!
# Cyclic Agree over articulated person probes

An articulated person probe is a set of unvalued person segments, in the simplest case a segment
together with the segments it entails, `Finset.Iic x`. A probe on v first meets the internal
argument, which checks every segment it bears; the segments left over, the residue, probe again
from the next projection of v, where the external argument is the closest goal. A context, the
scenario of the external over the internal argument, is direct when the external argument checks
some of the residue and inverse otherwise, and [the core probe licenses the external argument
exactly in direct contexts](##eaLicensed_iff_isDirect). When the segments of the probe form a chain
of entailments, [a context is direct exactly when it is
downstream](##isDirect_iff_kind_eq_downstream) on the number of probe segments each person bears,
the person hierarchy of the language.

## Implementation notes

A person bears its whole specification `Phi.PersonSegment.spec`, and a probe sees of it the
segments the probe has. Whether a language tells first from second person by [speaker] or by
[addressee] is therefore carried by its probe, `Finset.Iic .speaker` or `Finset.Iic .addressee`,
and not by a second parameter for the specifications of its nominals.

## References

* [bejar-rezac-2009]
* [harley-ritter-2002]
-/

@[expose] public section

namespace Minimalist.CyclicAgree

open Phi PersonSegment
open Clause (Scenario)

variable (P : Finset PersonSegment) (s : Scenario Person) (p q : Person) {x : PersonSegment}

/-! ### The residue and the two kinds of context -/

/-- The residue of a probe after Agree with a goal, the segments the goal does not bear. -/
def residue : Finset PersonSegment := P \ spec p

variable {P p} in
@[simp] theorem mem_residue : x ∈ residue P p ↔ x ∈ P ∧ x ∉ spec p := Finset.mem_sdiff

/-- A context, the scenario of the external over the internal argument, is direct when the
external argument bears some segment of the residue the internal argument leaves. -/
def IsDirect : Prop := (residue P s.low ∩ spec s.high).Nonempty

/-- A context is inverse when it is not direct. -/
abbrev IsInverse : Prop := ¬ IsDirect P s

instance : DecidablePred (IsDirect P) := fun _ ↦ inferInstanceAs (Decidable (Finset.Nonempty _))

variable {P s}

theorem isDirect_iff : IsDirect P s ↔ ∃ x ∈ P, x ∉ spec s.low ∧ x ∈ spec s.high := by
  simp [IsDirect, Finset.Nonempty, and_assoc]

/-- A context is direct when the internal argument does not bear every probe segment the external
argument bears. -/
theorem isDirect_iff_not_subset : IsDirect P s ↔ ¬ P ∩ spec s.high ⊆ spec s.low := by
  simp only [isDirect_iff, Finset.not_subset, Finset.mem_inter]
  exact ⟨fun ⟨x, hx, hl, hh⟩ ↦ ⟨x, ⟨hx, hh⟩, hl⟩, fun ⟨x, ⟨hx, hh⟩, hl⟩ ↦ ⟨x, hx, hl, hh⟩⟩

variable (P) in
theorem not_isDirect_self : ¬ IsDirect P ⟨p, p⟩ := fun h ↦
  isDirect_iff_not_subset.1 h Finset.inter_subset_right

/-- A probe with more segments has more direct contexts. -/
theorem IsDirect.mono {Q : Finset PersonSegment} (h : P ⊆ Q) (hd : IsDirect P s) :
    IsDirect Q s :=
  let ⟨x, hx, hl, hh⟩ := isDirect_iff.1 hd
  isDirect_iff.2 ⟨x, h hx, hl, hh⟩

/-- An internal argument bearing every segment of the probe leaves no residue. -/
theorem not_isDirect_of_subset (h : P ⊆ spec s.low) : ¬ IsDirect P s := fun hd ↦
  isDirect_iff_not_subset.1 hd (Finset.inter_subset_left.trans h)

variable (s) in
/-- The flat probe `[uπ]` makes every context inverse, since every internal argument bears `π`. -/
theorem not_isDirect_Iic_bot : ¬ IsDirect (Finset.Iic ⊥) s :=
  not_isDirect_of_subset fun x hx ↦ by
    rw [Finset.mem_Iic, le_bot_iff] at hx
    exact hx ▸ pi_mem_spec s.low

variable (P s)

/-- The person the agreement slot realizes, the external argument's in a direct context and the
internal argument's in an inverse one. -/
def value : Person := if IsDirect P s then s.high else s.low

/-! ### The person hierarchy of a probe -/

/-- The rank of a person on a probe's scale, the number of probe segments it bears. -/
def rank : ℕ := (P ∩ spec p).card

variable {P s}

/-- Of two persons, one bears every segment of a chain that the other bears. -/
private theorem inter_spec_subset_or (hP : IsChain (· ≤ ·) (P : Set PersonSegment)) :
    P ∩ spec p ⊆ spec q ∨ P ∩ spec q ⊆ spec p := by
  by_contra! h
  simp only [Finset.not_subset, Finset.mem_inter] at h
  obtain ⟨⟨x, ⟨hx, hxp⟩, hxq⟩, y, ⟨hy, hyq⟩, hyp⟩ := h
  rcases hP.total hx hy with hxy | hyx
  · exact hxq (spec_isLowerSet q hxy hyq)
  · exact hyp (spec_isLowerSet p hyx hxp)

theorem isDirect_of_rank_lt (h : rank P s.low < rank P s.high) : IsDirect P s :=
  isDirect_iff_not_subset.2 fun hsub ↦
    h.not_ge (Finset.card_le_card (Finset.subset_inter Finset.inter_subset_left hsub))

/-- When the segments of the probe form a chain, a context is direct iff the external argument
outranks the internal one. -/
theorem isDirect_iff_rank_lt (hP : IsChain (· ≤ ·) (P : Set PersonSegment)) :
    IsDirect P s ↔ rank P s.low < rank P s.high := by
  refine ⟨fun h ↦ ?_, isDirect_of_rank_lt⟩
  rw [isDirect_iff_not_subset] at h
  have hsub := (inter_spec_subset_or s.high s.low hP).resolve_left h
  exact Finset.card_lt_card
    ⟨Finset.subset_inter Finset.inter_subset_left hsub,
      fun h' ↦ h (h'.trans Finset.inter_subset_right)⟩

/-- When the segments of the probe form a chain, a context is direct iff it is downstream on the
probe's rank, so the inverse contexts are the balanced and upstream scenarios. -/
theorem isDirect_iff_kind_eq_downstream (hP : IsChain (· ≤ ·) (P : Set PersonSegment)) :
    IsDirect P s ↔ (s.map (rank P)).kind = .downstream :=
  (isDirect_iff_rank_lt hP).trans (Scenario.kind_eq_downstream_iff (s := s.map (rank P))).symm

/-! ### Licensing the external argument -/

/-- The segment `[uF]` of a probe, as a probe over persons: it interacts with the persons bearing
`F` and is satisfied by any person, since every person bears the root `π`, so that its search
halts at the closest goal whether or not that goal bears `F`. -/
def segmentProbe (x : PersonSegment) : Probe Person := (Probe.Spec.ofGeometry x ⊥).toProbe spec

variable (x) in
theorem segmentProbe_int : (segmentProbe x).int p ↔ x ∈ spec p :=
  Probe.Spec.ofGeometry_toProbe_int_iff fun _ hy _ hzy ↦ spec_isLowerSet p hzy hy

variable (x) in
theorem segmentProbe_sat : (segmentProbe x).sat p :=
  Probe.Spec.ofFeatures_toProbe_sat.2
    ⟨⊥, Finset.mem_inter.2 ⟨pi_mem_spec p, Finset.mem_singleton_self _⟩⟩

variable (x) in
/-- A segment Agrees with the closest goal iff that goal bears it, and with no other. -/
theorem segmentProbe_goal_cons (l : List Person) :
    (segmentProbe x).goal (p :: l) = if x ∈ spec p then some p else none := by
  simp [Probe.goal, Probe.search, segmentProbe_sat, segmentProbe_int, Option.filter]

variable (P s) in
/-- The external argument's person is licensed by the core probe when some segment of the residue
Agrees with it from the next projection of v, whose domain has the external argument closest and
the internal one below. -/
def EALicensed : Prop :=
  ∃ x ∈ residue P s.low, (segmentProbe x).goal [s.high, s.low] = some s.high

instance : DecidablePred (EALicensed P) := fun _ ↦
  inferInstanceAs (Decidable (∃ x ∈ residue P _, _))

/-- The core probe licenses the external argument exactly in direct contexts. -/
theorem eaLicensed_iff_isDirect : EALicensed P s ↔ IsDirect P s := by
  simp [EALicensed, IsDirect, Finset.Nonempty, segmentProbe_goal_cons]

end Minimalist.CyclicAgree
