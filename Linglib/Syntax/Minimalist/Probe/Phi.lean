module

public import Linglib.Syntax.Minimalist.Probe.Basic
public import Linglib.Syntax.Agreement.Bundle
public import Linglib.Syntax.Case.Basic

/-!
# φ-probes

This file specializes `Probe` to φ-features, as probes over `Agreement.Bundle`s relativized by
the feature they seek, among them Preminger's person probe π⁰, which seeks [participant], and
number probe #⁰, which seeks [plural], and the φ-goals they search, nominals with or without
valued Case.

## Main definitions

* `Minimalist.Probe.Target`, `Agreement.Bundle.visibleTo`: the features a relativized probe
  seeks, and the cells that bear them.
* `Minimalist.Probe.Target.toProbe`: a target's denotation as a `Probe` over φ-cells.
* `Minimalist.PhiGoal`: a nominal as a φ-goal, its case if already valued and its φ-cell.

## References

* [preminger-2014]
* [chomsky-2000]
-/

@[expose] public section

namespace Minimalist

/-- The feature a relativized φ-probe seeks. -/
inductive Probe.Target where
  /-- π⁰, the person probe, seeks [participant]. -/
  | participant
  /-- #⁰, the number probe, seeks [plural]. -/
  | plural
  deriving DecidableEq, Repr

/-- A φ-cell is visible to a relativized probe when it bears the feature the probe seeks; the
probe skips the cells that lack it. -/
def _root_.Agreement.Bundle.visibleTo (c : Agreement.Bundle) : Probe.Target → Bool
  | .participant => decide c.IsSAP
  | .plural => decide c.IsPlural

/-- A `Probe.Target` denotes the probe over φ-cells relativized to the feature it seeks, π⁰ being
`Probe.Target.participant.toProbe`. -/
def Probe.Target.toProbe (t : Probe.Target) : Probe Agreement.Bundle :=
  .relativized (·.visibleTo t)

/-- A goal of a φ-probe records the case a head of its own has valued, if any, and its φ-cell. A
relativized probe reads the cell for visibility, and Agree reads the case for activity, a goal
being active iff its case is unvalued, as an unchecked structural case feature renders a goal
active for [chomsky-2000]. -/
structure PhiGoal where
  valuedCase : Option Case
  cell : Agreement.Bundle
  deriving DecidableEq, Repr

/-- A goal is active, visible to Agree, iff its case is unvalued. -/
def PhiGoal.isActive (g : PhiGoal) : Bool := g.valuedCase.isNone

/-- `PhiGoal.valued c cell` is a nominal whose case `c` a head of its own has already valued, so
that it is inactive for Agree. -/
def PhiGoal.valued (c : Case) (cell : Agreement.Bundle) : PhiGoal := ⟨some c, cell⟩

/-- `PhiGoal.unvalued cell` is a nominal with unvalued case, so that it is active for Agree. -/
def PhiGoal.unvalued (cell : Agreement.Bundle) : PhiGoal := ⟨none, cell⟩

@[simp] theorem PhiGoal.cell_valued (c : Case) (cell : Agreement.Bundle) :
    (PhiGoal.valued c cell).cell = cell := rfl

@[simp] theorem PhiGoal.valuedCase_valued (c : Case) (cell : Agreement.Bundle) :
    (PhiGoal.valued c cell).valuedCase = some c := rfl

@[simp] theorem PhiGoal.cell_unvalued (cell : Agreement.Bundle) :
    (PhiGoal.unvalued cell).cell = cell := rfl

@[simp] theorem PhiGoal.valuedCase_unvalued (cell : Agreement.Bundle) :
    (PhiGoal.unvalued cell).valuedCase = none := rfl

@[simp] theorem PhiGoal.isActive_valued (c : Case) (cell : Agreement.Bundle) :
    (PhiGoal.valued c cell).isActive = false := rfl

@[simp] theorem PhiGoal.isActive_unvalued (cell : Agreement.Bundle) :
    (PhiGoal.unvalued cell).isActive = true := rfl

@[simp] theorem PhiGoal.valued_ne_unvalued (c : Case) (cell cell' : Agreement.Bundle) :
    PhiGoal.valued c cell ≠ PhiGoal.unvalued cell' := by
  simp [PhiGoal.valued, PhiGoal.unvalued]

@[simp] theorem PhiGoal.unvalued_ne_valued (c : Case) (cell cell' : Agreement.Bundle) :
    PhiGoal.unvalued cell' ≠ PhiGoal.valued c cell :=
  (PhiGoal.valued_ne_unvalued c cell cell').symm

end Minimalist
