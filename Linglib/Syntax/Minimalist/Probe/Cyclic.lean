module

public import Linglib.Syntax.Person.Segment
public import Linglib.Syntax.Clause.Scenario
public import Linglib.Syntax.Minimalist.Probe.Agree

/-!
# Cyclic Agree over articulated person probes

An articulated person probe is a set of unvalued person segments, in the simplest case a segment
together with the segments it entails, `Finset.Iic x`. A probe on v first meets the internal
argument, which checks every segment it bears; the segments left over, the residue, probe again
from the next projection of v, where the external argument is the closest goal. A context, the
scenario of the external over the internal argument, is inverse when the internal argument is at
least as specified as the external one relative to the probe (`Minimalist.SpecLE`) and
direct otherwise, and [the core probe licenses the external argument exactly in direct
contexts](##eaLicensed_iff_isDirect). When the segments of the probe form a chain of entailments,
[a context is direct exactly when it is downstream](##isDirect_iff_kind_eq_downstream) on the
number of probe segments each person bears, the person hierarchy of the language.

## Implementation notes

Béjar and Rezac specify persons per language, a second person as [participant] alone where
the first bears [speaker] and a first person so where the second bears [addressee]. Here a
person bears its whole specification `PersonSegment.spec`, and a probe sees of it the segments
the probe has, which are the person's specification in the probe's features
(`PersonSegment.inter_spec`). The language's choice is therefore carried by its probe,
`Finset.Iic .speaker` or `Finset.Iic .addressee`, and not by a second parameter.

## References

* [bejar-rezac-2009]
* [harley-ritter-2002]
* [coon-keine-2021]
-/

@[expose] public section

namespace Minimalist

/-! ### Specification relative to a set of features -/

section SpecLE

variable {F : Type*} [DecidableEq F] {P Q s t u : Finset F}

/-- Relative to the features `P`, the feature set `t` is at least as specified as `s`: it has
every feature of `P` that `s` has. With `P` the segments of a probe, this compares two goals
"relative to the specification of the probe" ([coon-keine-2021]). -/
def SpecLE (P s t : Finset F) : Prop := P ∩ s ⊆ t

instance : Decidable (SpecLE P s t) := inferInstanceAs (Decidable (P ∩ s ⊆ t))

theorem specLE_iff : SpecLE P s t ↔ ∀ x ∈ P, x ∈ s → x ∈ t := by
  simp [SpecLE, Finset.subset_iff]

@[refl] theorem SpecLE.refl (P s : Finset F) : SpecLE P s s := Finset.inter_subset_right

@[trans] theorem SpecLE.trans (h₁ : SpecLE P s t) (h₂ : SpecLE P t u) : SpecLE P s u :=
  fun _ hx ↦ h₂ (Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hx).1, h₁ hx⟩)

/-- Fewer features tell fewer feature sets apart. -/
theorem SpecLE.anti (h : P ⊆ Q) (hQ : SpecLE Q s t) : SpecLE P s t :=
  (Finset.inter_subset_inter_right h).trans hQ

theorem SpecLE.of_subset (h : s ⊆ t) : SpecLE P s t := Finset.inter_subset_right.trans h

@[simp] theorem specLE_univ [Fintype F] : SpecLE Finset.univ s t ↔ s ⊆ t := by simp [SpecLE]

theorem SpecLE.card_le (h : SpecLE P s t) : (P ∩ s).card ≤ (P ∩ t).card :=
  Finset.card_le_card (Finset.subset_inter Finset.inter_subset_left h)

variable [Preorder F]

/-- On a chain of features any two lower sets are comparable. -/
theorem specLE_total (hP : IsChain (· ≤ ·) (P : Set F)) (hs : IsLowerSet (s : Set F))
    (ht : IsLowerSet (t : Set F)) : SpecLE P s t ∨ SpecLE P t s := by
  by_contra! h
  simp only [SpecLE, Finset.not_subset, Finset.mem_inter] at h
  obtain ⟨⟨x, ⟨hx, hxs⟩, hxt⟩, y, ⟨hy, hyt⟩, hys⟩ := h
  rcases hP.total hx hy with hxy | hyx
  · exact hxt (ht hxy hyt)
  · exact hys (hs hyx hxs)

/-- On a chain of features lower sets are compared by how many of the features they have. -/
theorem specLE_iff_card_le (hP : IsChain (· ≤ ·) (P : Set F)) (hs : IsLowerSet (s : Set F))
    (ht : IsLowerSet (t : Set F)) : SpecLE P s t ↔ (P ∩ s).card ≤ (P ∩ t).card := by
  refine ⟨SpecLE.card_le, fun h ↦ (specLE_total hP hs ht).elim id fun hts ↦ ?_⟩
  rw [SpecLE, ← Finset.eq_of_subset_of_card_le (Finset.subset_inter Finset.inter_subset_left hts) h]
  exact Finset.inter_subset_right

end SpecLE

/-- The third person, bearing the root alone, is the least specified person on any segments. -/
theorem specLE_third (P : Finset PersonSegment) (q : Person) :
    SpecLE P (PersonSegment.spec .third) (PersonSegment.spec q) :=
  .of_subset fun x hx ↦ by
    rw [show PersonSegment.spec Person.third = {.pi} by decide, Finset.mem_singleton] at hx
    exact hx ▸ PersonSegment.pi_mem_spec q

end Minimalist

namespace Minimalist.CyclicAgree

open PersonSegment
open Clause (Scenario)

variable (P : Finset PersonSegment) (s : Scenario Person) (p q : Person) {x : PersonSegment}

/-! ### The residue and the two kinds of context -/

/-- The residue of a probe after Agree with a goal, the segments the goal does not bear. -/
def residue : Finset PersonSegment := P \ spec p

variable {P p} in
@[simp] theorem mem_residue : x ∈ residue P p ↔ x ∈ P ∧ x ∉ spec p := Finset.mem_sdiff

/-- A context, the scenario of the external over the internal argument, is inverse when the
internal argument is at least as specified as the external one relative to the probe, so that it
leaves no residue the external argument could check. -/
def IsInverse : Prop := SpecLE P (spec s.high) (spec s.low)

/-- A context is direct when it is not inverse: the external argument bears some segment of the
residue the internal argument leaves. -/
def IsDirect : Prop := ¬ IsInverse P s

instance : DecidablePred (IsInverse P) := fun _ ↦ inferInstanceAs (Decidable (SpecLE P _ _))

instance : DecidablePred (IsDirect P) := fun _ ↦ inferInstanceAs (Decidable (¬ _))

variable {P s}

@[simp] theorem not_isDirect : ¬ IsDirect P s ↔ IsInverse P s := not_not

theorem isDirect_iff : IsDirect P s ↔ ∃ x ∈ P, x ∉ spec s.low ∧ x ∈ spec s.high := by
  simp only [IsDirect, IsInverse, specLE_iff, not_forall]
  exact ⟨fun ⟨x, hx, hh, hl⟩ ↦ ⟨x, hx, hl, hh⟩, fun ⟨x, hx, hl, hh⟩ ↦ ⟨x, hx, hh, hl⟩⟩

/-- A context is direct iff the external argument bears some segment of the residue. -/
theorem isDirect_iff_nonempty : IsDirect P s ↔ (residue P s.low ∩ spec s.high).Nonempty := by
  simp [isDirect_iff, Finset.Nonempty, and_assoc]

variable (P) in
theorem isInverse_self : IsInverse P ⟨p, p⟩ := .refl P _

/-- A probe with more segments has more direct contexts. -/
theorem IsDirect.mono {Q : Finset PersonSegment} (h : P ⊆ Q) (hd : IsDirect P s) :
    IsDirect Q s :=
  fun hi ↦ hd (hi.anti h)

/-- An internal argument bearing every segment of the probe leaves no residue. -/
theorem isInverse_of_subset (h : P ⊆ spec s.low) : IsInverse P s :=
  Finset.inter_subset_left.trans h

variable (s) in
/-- The flat probe `[uπ]` makes every context inverse, since every internal argument bears `π`. -/
theorem isInverse_Iic_bot : IsInverse (Finset.Iic ⊥) s :=
  isInverse_of_subset fun x hx ↦ by
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

/-- On the probe with [speaker] and what it depends on, a person's rank is its prominence, one
higher for the root: the probe's hierarchy is the person hierarchy 1 > 2 > 3. -/
theorem rank_Iic_speaker (p : Person) : rank (Finset.Iic .speaker) p = p.prominence + 1 := by
  cases p <;> decide

theorem isDirect_of_rank_lt (h : rank P s.low < rank P s.high) : IsDirect P s :=
  fun hi ↦ h.not_ge hi.card_le

/-- When the segments of the probe form a chain, a context is direct iff the external argument
outranks the internal one. -/
theorem isDirect_iff_rank_lt (hP : IsChain (· ≤ ·) (P : Set PersonSegment)) :
    IsDirect P s ↔ rank P s.low < rank P s.high :=
  (not_congr (specLE_iff_card_le hP (spec_isLowerSet _) (spec_isLowerSet _))).trans not_le

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
  simp [EALicensed, isDirect_iff_nonempty, Finset.Nonempty, segmentProbe_goal_cons]

end Minimalist.CyclicAgree
