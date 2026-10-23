module

public import Linglib.Data.Examples.EngelhardtEtAl2006
public import Linglib.Semantics.Reference.Distinguishing
public import Mathlib.Data.Fin.VecNotation

/-!
# Engelhardt et al. (2006): Do Speakers and Listeners Observe the Gricean Maxim of Quantity?

This file formalizes the reading of the maxim of Quantity for referring expressions in
[engelhardt-etal-2006]. A description of an object in a display under-describes when it does
not identify the object and over-describes when its modifier is not needed to identify it, and
the instructions of the paper's experiments are classified this way over its one-referent and
two-referent displays. Identification is `Distinguishes` against every other object
of the display.

## Implementation notes

* A display is five objects, each a kind with the object it rests on, so that *the towel* is
  ambiguous between the towel under the apple and the empty one and *the other towel* excludes
  the former.
* Over-description is measured against the bare noun, the paper's one contrast. The production
  rates, ratings and fixation data are not formalized.
* The examples are `Data.Examples.EngelhardtEtAl2006`.

## References

* [engelhardt-etal-2006]
* [grice-1975]
-/

@[expose] public section

namespace EngelhardtEtAl2006

open EngelhardtEtAl2006.Examples

/-- The kinds of object in a display, the apple to be moved, the frog, and the two kinds of
destination. -/
inductive Kind
  | apple
  | frog
  | towel
  | box
  deriving DecidableEq, Repr

/-- An object of a display, with its kind and the object it rests on or in, if any. -/
structure Object where
  kind : Kind
  support : Option (Fin 5) := none
  deriving DecidableEq, Repr

/-- A display of five objects, the target first and the object it rests on second. -/
abbrev Display := Fin 5 → Object

/-- The one-referent display, an apple on a towel, a frog, an empty towel and an empty box. -/
def oneReferent : Display := ![⟨.apple, some 1⟩, ⟨.towel, none⟩, ⟨.frog, none⟩, ⟨.towel, none⟩,
  ⟨.box, none⟩]

/-- The two-referent display, an apple on a towel, a second apple by itself, an empty towel and
an empty box. -/
def twoReferent : Display := ![⟨.apple, some 1⟩, ⟨.towel, none⟩, ⟨.apple, none⟩, ⟨.towel, none⟩,
  ⟨.box, none⟩]

/-! ### Descriptions and the maxim -/

/-- A referring expression of the instructions, a bare noun, a noun with a prepositional-phrase
modifier naming what the referent rests on, or *the other* noun, which excludes the object the
target rests on. -/
inductive Description
  | bare (k : Kind)
  | on (k loc : Kind)
  | other (k : Kind)
  deriving DecidableEq, Repr

/-- The noun of a description. -/
def Description.kind : Description → Kind
  | .bare k | .on k _ | .other k => k

/-- The bare noun a description is measured against. -/
def Description.bareOf (d : Description) : Description := .bare d.kind

/-- The description holds of an object of the display, *other* read relative to the target
`t`. -/
def extension (D : Display) (t : Fin 5) : Description → Fin 5 → Prop
  | .bare k, i => (D i).kind = k
  | .on k loc, i => (D i).kind = k ∧ ∃ j, (D i).support = some j ∧ (D j).kind = loc
  | .other k, i => (D i).kind = k ∧ (D t).support ≠ some i

instance (D : Display) (t : Fin 5) (d : Description) (i : Fin 5) : Decidable (extension D t d i) :=
  by cases d <;> unfold extension <;> infer_instance

/-- The description lets the addressee identify the intended referent `r` against every other
object of the display. -/
abbrev Identifies (D : Display) (t r : Fin 5) (d : Description) : Prop :=
  Distinguishes (extension D t) (Finset.univ.erase r) r d

/-- The description identifies `r` with a modifier its bare noun does not need. -/
def OverDescribes (D : Display) (t r : Fin 5) (d : Description) : Prop :=
  d ≠ d.bareOf ∧ Identifies D t r d ∧ Identifies D t r d.bareOf

instance (D : Display) (t r : Fin 5) (d : Description) : Decidable (OverDescribes D t r d) := by
  unfold OverDescribes; infer_instance

theorem oneReferent_target :
    Identifies oneReferent 0 0 (.bare .apple) ∧
      OverDescribes oneReferent 0 0 (.on .apple .towel) := by
  decide

theorem twoReferent_target :
    ¬ Identifies twoReferent 0 0 (.bare .apple) ∧ Identifies twoReferent 0 0 (.on .apple .towel) ∧
      ¬ OverDescribes twoReferent 0 0 (.on .apple .towel) := by
  decide

theorem destinations :
    ∀ D ∈ [oneReferent, twoReferent],
      ¬ Identifies D 0 3 (.bare .towel) ∧ Identifies D 0 3 (.other .towel) ∧
        ¬ OverDescribes D 0 3 (.other .towel) ∧ Identifies D 0 4 (.bare .box) := by
  decide

/-! ### The instructions -/

/-- An instruction, *Put the apple … in/on the …*, with its target and destination
descriptions. -/
structure Instruction where
  target : Description
  destination : Description
  deriving DecidableEq, Repr

/-- The target descriptions as named in the rows. -/
def targetTable : List (String × Description) :=
  [("bare", .bare .apple), ("modified", .on .apple .towel)]

/-- The destination descriptions as named in the rows. -/
def destinationTable : List (String × Description) :=
  [("towel", .bare .towel), ("otherTowel", .other .towel), ("box", .bare .box)]

/-- An instruction from an example row. -/
def Instruction.ofDatum (ex : Datum) : Option Instruction := do
  pure ⟨← ex.parse? "target" targetTable, ← ex.parse? "destination" destinationTable⟩

theorem ofDatum_isSome :
    ∀ ex ∈ Examples.all, (ex.feature? "target").isSome → (Instruction.ofDatum ex).isSome := by
  decide

/-- The four instructions of the paper's table. -/
def instructions : List Instruction := Examples.all.filterMap Instruction.ofDatum

/-- The destination matches the target's current location, a towel. -/
def Instruction.Matching (ins : Instruction) : Prop := ins.destination.kind = .towel

/-- The intended destination in either display: the empty towel or the box. -/
def Instruction.goal (ins : Instruction) : Fin 5 := if ins.destination.kind = .towel then 3 else 4

theorem instructions_destination :
    ∀ D ∈ [oneReferent, twoReferent], ∀ ins ∈ instructions,
      (Identifies D 0 ins.goal ins.destination ↔ ins.destination ≠ .bare .towel) ∧
        ¬ OverDescribes D 0 ins.goal ins.destination := by
  decide

theorem instructions_oneReferent :
    ∀ ins ∈ instructions,
      Identifies oneReferent 0 0 ins.target ∧
        (OverDescribes oneReferent 0 0 ins.target ↔ ins.target ≠ .bare .apple) := by
  decide

theorem instructions_twoReferent :
    ∀ ins ∈ instructions,
      (Identifies twoReferent 0 0 ins.target ↔ ins.target ≠ .bare .apple) ∧
        ¬ OverDescribes twoReferent 0 0 ins.target := by
  decide

end EngelhardtEtAl2006
