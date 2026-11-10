module

public import Linglib.Syntax.Minimalist.Clause.Spine
public import Mathlib.Order.Monotone.Defs

/-!
# Probe profiles

A probe's locality profile is the head that hosts it together with its horizon, the category that
terminates its search. Category features are inherited up an extended projection, so a clause
carries every head it projects, and a clause is transparent to a probe exactly when it does not
project the horizon. Larger clauses are then
[at least as opaque](##Minimalist.Probe.Profile.transparentTo_antitone), which is Upward
Entailment. A probe whose horizon lies in its own complement is vacuous: its search ends at its
sister. A nonvacuous probe therefore searches into
[every clause inside its complement](##Minimalist.Probe.Profile.TransparentTo.of_not_isVacuousIn),
and a horizon makes vacuous
[every probe hosted above it](##Minimalist.Probe.Profile.IsVacuousIn.of_mem_below), the two
halves of the Height–Locality Theorem.

## Implementation notes

Vacuity is relative to the spine that hosts the probe, and the probe's sister is
`ClauseSpine.below` of its head. On a spine that does not project the probe's head the complement
is the whole spine, so vacuity is meaningful only for a head the spine projects.

## TODO

* Transparency reads a clause's label; `Minimalist.horizon` cuts the positions of a tree behind a
  head of the horizon category. No theorem yet says that the positions inside a clause opaque to
  a probe lie behind its horizon, which needs projections labelled by their spines.

## References

* [keine-2019]
* [keine-2020]
-/

@[expose] public section

namespace Minimalist

/-- A probe's profile is the head that hosts it and the category that terminates its search, its
horizon; a probe without horizon searches into any domain. -/
structure Probe.Profile where
  /-- The head that hosts the probe. -/
  probeHead : Cat
  /-- The category that terminates the probe's search, if any. -/
  horizon : Option Cat
  deriving DecidableEq, Repr

namespace Probe.Profile

variable (p : Probe.Profile) {s t : ClauseSpine} {c d h : Cat} {o : Option Cat}

/-! ### Transparency -/

/-- A clause is transparent to `p` when `p` has no horizon or the clause does not project it. -/
def TransparentTo (s : ClauseSpine) : Prop := ∀ h ∈ p.horizon, h ∉ s

instance : Decidable (p.TransparentTo s) := Option.decidableForallMem _

@[simp] theorem transparentTo_mk_none : (Probe.Profile.mk c none).TransparentTo s := by
  simp [TransparentTo]

@[simp] theorem transparentTo_mk_some : (Probe.Profile.mk c (some h)).TransparentTo s ↔ h ∉ s := by
  simp [TransparentTo]

variable {p}

theorem TransparentTo.anti (hst : s ≤ t) (ht : p.TransparentTo t) : p.TransparentTo s :=
  fun c hc hm ↦ ht c hc (ClauseSpine.le_iff_forall_mem.1 hst c hm)

variable (p) in
/-- Upward Entailment: a clause opaque to a probe stays opaque when it projects more structure,
since it inherits the horizon from the smaller clause. -/
theorem transparentTo_antitone : Antitone p.TransparentTo := fun _ _ ↦ TransparentTo.anti

/-! ### Vacuity -/

variable (p) in
/-- `p` is vacuous in `s` when its horizon lies in the complement of its head, so that its search
ends at its sister and it triggers no movement or agreement. -/
def IsVacuousIn (s : ClauseSpine) : Prop := ¬ p.TransparentTo (s.below p.probeHead)

instance : Decidable (p.IsVacuousIn s) := inferInstanceAs (Decidable (¬ _))

theorem isVacuousIn_iff : p.IsVacuousIn s ↔ ∃ h ∈ p.horizon, h ∈ s.below p.probeHead := by
  simp [IsVacuousIn, TransparentTo]

@[simp] theorem not_isVacuousIn_mk_none : ¬ (Probe.Profile.mk c none).IsVacuousIn s :=
  not_not_intro transparentTo_mk_none

@[simp] theorem isVacuousIn_mk_some :
    (Probe.Profile.mk c (some h)).IsVacuousIn s ↔ h ∈ s.below c := by
  simp [IsVacuousIn]

/-- A probe whose horizon is the category of its own head, its default horizon, is not vacuous. -/
theorem not_isVacuousIn_mk_self : ¬ (Probe.Profile.mk c (some c)).IsVacuousIn s := by
  simpa using s.notMem_below_self c

/-- The Height–Locality Theorem, from height to locality: a nonvacuous probe searches into every
clause that projects no more than its complement does. -/
theorem TransparentTo.of_not_isVacuousIn (hp : ¬ p.IsVacuousIn s) (ht : t ≤ s.below p.probeHead) :
    p.TransparentTo t :=
  (not_not.1 hp).anti ht

/-- The Height–Locality Theorem, from locality to height: a horizon that makes a probe on `c`
vacuous makes vacuous a probe on any head above `c`. -/
theorem IsVacuousIn.of_mem_below (hp : (Probe.Profile.mk c o).IsVacuousIn s)
    (hc : c ∈ s.below d) : (Probe.Profile.mk d o).IsVacuousIn s :=
  fun ht ↦ hp (ht.anti (ClauseSpine.below_le_below hc))

end Probe.Profile

end Minimalist
