/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Locality.Transfer

/-!
# Horizons

A probe's search stops at a head of its horizon category: what that head c-commands, its
complement, is beyond the probe's reach. A horizon is thus the cut Transfer makes, the complements
of a set of heads, indexed by the probe and its category rather than by the stage of the
derivation.

## Main definitions

* `Minimalist.horizon`: the positions behind the horizon of a category for the probe at a
  position.

## Main results

* `Minimalist.horizon_eq_sealed`: a horizon is the cut of the complements of the horizon heads
  the probe c-commands, transferred at every stage.

## References

* [keine-2019]
* [keine-2020]
-/

@[expose] public section

namespace Minimalist

open Core.Order RoseTree

variable (t : LinearizedSyntacticObject)

/-- The heads of category `c` the probe at `a` c-commands. -/
def horizonHeads (a : TreePath) (c : Cat) : Finset TreePath :=
  ((occurrencesWith t (·.item.cat = c)).filter fun h ↦ decide (t.val.CCommands a h)).toFinset

/-- The positions behind the horizon `c` of the probe at `a`, in the complement of a head of
category `c` the probe c-commands ([keine-2019]). -/
def horizon (a : TreePath) (c : Cat) : Set TreePath :=
  {q | ∃ h ∈ horizonHeads t a c, complement h ≤ q}

instance (a : TreePath) (c : Cat) : DecidablePred (· ∈ horizon t a c) :=
  fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

variable {t}

theorem isUpperSet_horizon {a : TreePath} {c : Cat} : IsUpperSet (horizon t a c) :=
  fun _ _ hqr ⟨h, hh, hq⟩ ↦ ⟨h, hh, hq.trans hqr⟩

theorem horizon_eq_sealed (hd : HeadFunction) (a s : TreePath) (c : Cat) :
    horizon t a c = sealed (horizonHeads t a c) (complementDomain hd t ∅) (fun _ _ _ ↦ True) s := by
  ext q
  simp [horizon, sealed, complementDomain, transferHead]

end Minimalist
