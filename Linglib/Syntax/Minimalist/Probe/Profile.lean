module

public import Linglib.Syntax.Minimalist.Clause.Spine
public import Linglib.Syntax.Minimalist.Probe.Basic
public import Mathlib.Data.Finset.Empty
public import Mathlib.Order.Monotone.Defs

/-!
# Probe profiles

This file defines a probe's locality profile, the head that hosts it together with the category
that terminates its search, its horizon. Keine labels a clause bilaterally, by the set of heads
it projects, and a clause is transparent to a probe exactly when its label does not contain the
horizon. Transparency is then antitone in the extension order of clause spines, which is Upward
Entailment, and a probe whose horizon lies in the label of its own sister is vacuous, the premise
of the Height–Locality Theorem. A horizon cuts the domain a probe searches
(`Probe.Inspects.of_subset`); on positions it is `Minimalist.horizon`.

## Main definitions

* `Minimalist.Probe.Profile`: the head hosting a probe and the category that is its horizon.
* `Minimalist.Probe.Profile.TransparentTo`: a bilateral label not containing the horizon.
* `Minimalist.Probe.Profile.IsVacuous`: a horizon lying in the label of the probe's sister on the
  standard verbal spine.

## Main results

* `Minimalist.Probe.Profile.transparentTo_label_antitone`: Upward Entailment.

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

variable (p : Probe.Profile) {L L₁ L₂ : Finset Cat}

/-! ### Transparency -/

/-- A domain with bilateral label `L` is transparent to `p` when `p` has no horizon or the label
does not contain it. -/
def TransparentTo (L : Finset Cat) : Prop := ∀ h ∈ p.horizon, h ∉ L

instance : Decidable (p.TransparentTo L) := Option.decidableForallMem _

@[simp] theorem transparentTo_mk_none (head : Cat) (L : Finset Cat) :
    (Probe.Profile.mk head none).TransparentTo L := by
  simp [TransparentTo]

@[simp] theorem transparentTo_mk_some {head h : Cat} :
    (Probe.Profile.mk head (some h)).TransparentTo L ↔ h ∉ L := by
  simp [TransparentTo]

variable {p}

/-- Upward Entailment. A label containing every head of a label opaque to `p` is opaque to `p`. -/
theorem TransparentTo.anti (h : L₁ ⊆ L₂) (hL : p.TransparentTo L₂) : p.TransparentTo L₁ :=
  fun c hc hm ↦ hL c hc (h hm)

variable (p)

/-- Upward Entailment. Transparency is antitone in the extension order of clause spines, since a
spine's label contains the horizon whenever a spine below it does. -/
theorem transparentTo_label_antitone : Antitone fun s : ClauseSpine ↦ p.TransparentTo s.label :=
  fun _ _ h ht ↦ ht.anti h

/-! ### Vacuity -/

/-- The label of the sister of a head on the standard verbal spine, TP under C⁰, CP under Force⁰
and vP under T⁰. -/
def sisterLabel : Cat → Finset Cat
  | .C => ClauseSpine.tP.label
  | .Force => ClauseSpine.cP.label
  | .T => ClauseSpine.vP.label
  | _ => ∅

/-- `p` is vacuous when its horizon lies in the label of its sister on the standard verbal spine,
so that its search terminates at its sister and no domain remains. Vacuous probes trigger no
dependency and are undetectable, which is what makes the Height–Locality Theorem emerge. -/
def IsVacuous : Prop := ¬ p.TransparentTo (sisterLabel p.probeHead)

instance : Decidable p.IsVacuous := inferInstanceAs (Decidable (¬ _))

/-- A probe without horizon is never vacuous. -/
@[simp] theorem not_isVacuous_mk_none (head : Cat) : ¬ (Probe.Profile.mk head none).IsVacuous :=
  not_not_intro (transparentTo_mk_none head _)

end Probe.Profile

end Minimalist
