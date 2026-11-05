module

public import Linglib.Data.Examples.EngelhardtEtAl2006
public import Linglib.Semantics.Reference.Distinguishing
public import Mathlib.Data.Fin.VecNotation
public import Linglib.Data.Examples.Readers

/-!
# Engelhardt, Bailey and Ferreira (2006): Do Speakers and Listeners Observe the Gricean Maxim of Quantity?

This file formalizes the maxim of Quantity for the descriptions in Engelhardt, Bailey and
Ferreira's instructions. A description under-describes an object when it does not distinguish it
from the other objects, and over-describes it when it has a modifier its bare noun does not need.
With one apple [only *put the apple in the box* observes the maxim](##observesQuantity_table1),
and [with *the other towel* for *the towel*](##observesQuantity_instructions2b) the instructions
differ only in over-describing the apple. [*The towel* under-describes the empty
towel](##towel_destination) against the display, not among the places the apple can be moved to.
The Referential Model's [support for an analysis](##supports_iff_exists_observesQuantity) is the
maxim for the target alone, so with one apple [it takes *on the towel* as the
destination](##supports_oneReferent_twoReferent), which then under-describes.

## Implementation notes

* Destinations are judged against the whole display; the production rates, ratings and
  fixations are not formalized.

## Errata

* p. 561 places the over-descriptions in "the former", two-referent, condition; [they are in the
  one-referent display](##observesQuantity_table1).

## TODO

* Pair the ratings of Experiments 2 and 2b with `Instruction.ObservesQuantity` from a
  `Data/Statistics` table.

## References

* [engelhardt-etal-2006]
* [grice-1975]
* [altmann-steedman-1988]
-/

@[expose] public section

namespace EngelhardtEtAl2006

open EngelhardtEtAl2006.Examples Finset

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

/-- A display of five objects, the target first. -/
abbrev Display := Fin 5 → Object

/-- The one-referent display, an apple on a towel, a frog, an empty towel and an empty box. -/
def oneReferent : Display := ![⟨.apple, some 1⟩, ⟨.towel, none⟩, ⟨.frog, none⟩, ⟨.towel, none⟩,
  ⟨.box, none⟩]

/-- The two-referent display, an apple on a towel, a second apple by itself, an empty towel and
an empty box. -/
def twoReferent : Display := ![⟨.apple, some 1⟩, ⟨.towel, none⟩, ⟨.apple, none⟩, ⟨.towel, none⟩,
  ⟨.box, none⟩]

/-- The objects the target can be moved to: all but the target and the object it rests on. -/
def destinations (D : Display) : Finset (Fin 5) := {i | i ≠ 0 ∧ (D 0).support ≠ some i}

/-! ### Descriptions and the maxim -/

/-- A description in the instructions, a bare noun, a noun with a prepositional-phrase modifier
naming what the referent rests on, or *the other* noun. -/
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

/-- The description holds of an object of the display, *other* excluding the object the target
rests on. -/
def extension (D : Display) : Description → Fin 5 → Prop
  | .bare k, i => (D i).kind = k
  | .on k loc, i => (D i).kind = k ∧ ∃ j, (D i).support = some j ∧ (D j).kind = loc
  | .other k, i => (D i).kind = k ∧ (D 0).support ≠ some i

instance (D : Display) (d : Description) (i : Fin 5) : Decidable (extension D d i) := by
  cases d <;> unfold extension <;> infer_instance

/-- The description identifies `r` among the objects `s`: it holds of `r` and of no other member
of `s`. -/
abbrev Identifies (D : Display) (s : Finset (Fin 5)) (r : Fin 5) (d : Description) : Prop :=
  Distinguishes (extension D) (s.erase r) r d

/-- The description identifies `r` among `s` with a modifier its bare noun does not need. -/
def OverDescribes (D : Display) (s : Finset (Fin 5)) (r : Fin 5) (d : Description) : Prop :=
  d ≠ d.bareOf ∧ Identifies D s r d ∧ Identifies D s r d.bareOf

instance (D : Display) (s : Finset (Fin 5)) (r : Fin 5) (d : Description) :
    Decidable (OverDescribes D s r d) := by
  unfold OverDescribes; infer_instance

/-- The description observes the maxim of Quantity for `r` among `s`: it identifies `r` without
over-describing it. -/
def ObservesQuantity (D : Display) (s : Finset (Fin 5)) (r : Fin 5) (d : Description) : Prop :=
  Identifies D s r d ∧ ¬ OverDescribes D s r d

instance (D : Display) (s : Finset (Fin 5)) (r : Fin 5) (d : Description) :
    Decidable (ObservesQuantity D s r d) := by
  unfold ObservesQuantity; infer_instance

/-- *The towel* fails to identify the empty towel against the display but observes the maxim
among the objects the apple can be moved to, and *the other towel* observes it against the
display (pp. 561, 569). -/
theorem towel_destination :
    ∀ D ∈ [oneReferent, twoReferent],
      ¬ Identifies D univ 3 (.bare .towel) ∧ ObservesQuantity D (destinations D) 3 (.bare .towel) ∧
        ObservesQuantity D univ 3 (.other .towel) := by
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

-- every row with a target reads as an instruction
example :
    ∀ ex ∈ Examples.all, (ex.feature? "target").isSome → (Instruction.ofDatum ex).isSome := by
  decide

/-- The four instructions of Table 1. -/
def instructions : List Instruction := Examples.all.filterMap Instruction.ofDatum

/-- The instructions of Experiment 2b, Table 1's with *put the apple on the other towel* for *put
the apple on the towel*. -/
def instructions2b : List Instruction :=
  instructions.map fun ins ↦
    if ins.destination = .bare .towel then { ins with destination := .other .towel } else ins

/-- The object an instruction moves the target to in either display, the empty towel or the
box. -/
def Instruction.goal (ins : Instruction) : Fin 5 := if ins.destination.kind = .towel then 3 else 4

/-- An instruction observes the maxim of Quantity in a display when its target and destination
descriptions do against the whole display. -/
def Instruction.ObservesQuantity (D : Display) (ins : Instruction) : Prop :=
  EngelhardtEtAl2006.ObservesQuantity D univ 0 ins.target ∧
    EngelhardtEtAl2006.ObservesQuantity D univ ins.goal ins.destination

instance (D : Display) (ins : Instruction) : Decidable (ins.ObservesQuantity D) := by
  unfold Instruction.ObservesQuantity; infer_instance

/-- Of the instructions of Table 1, only *put the apple in the box* observes the maxim in the
one-referent display, and in the two-referent display those with a modified target do (p. 561). -/
theorem observesQuantity_table1 :
    ∀ ins ∈ instructions,
      (ins.ObservesQuantity oneReferent ↔ ins = ⟨.bare .apple, .bare .box⟩) ∧
        (ins.ObservesQuantity twoReferent ↔ ins.target ≠ .bare .apple) := by
  decide

/-- In the one-referent display each instruction of Experiment 2b identifies its target and
observes the maxim for its destination, and it over-describes the target exactly when the target
is modified (p. 564). -/
theorem observesQuantity_instructions2b :
    ∀ ins ∈ instructions2b,
      Identifies oneReferent univ 0 ins.target ∧
        ObservesQuantity oneReferent univ ins.goal ins.destination ∧
          (OverDescribes oneReferent univ 0 ins.target ↔ ins.target ≠ .bare .apple) := by
  decide

/-! ### The Referential Model -/

/-- The two analyses of *on the towel* in *put the apple on the towel …*, as the location the apple
is to be put, or as a modifier of *the apple*. -/
inductive Attachment
  | location
  | modifier
  deriving DecidableEq, Fintype, Repr

/-- The description of the target under an analysis. -/
def Attachment.target : Attachment → Description
  | .location => .bare .apple
  | .modifier => .on .apple .towel

/-- A display supports an analysis when its target description identifies some object and, for
the modifier, the bare noun identifies none, as in the Referential Model of
[altmann-steedman-1988]. -/
def Supports (D : Display) (a : Attachment) : Prop :=
  (∃ r, Identifies D univ r a.target) ∧ (a = .modifier → ¬ ∃ r, Identifies D univ r (.bare .apple))

instance (D : Display) (a : Attachment) : Decidable (Supports D a) := by
  unfold Supports; infer_instance

/-- A display supports an analysis exactly when its target description observes the maxim of
Quantity for some object. -/
theorem supports_iff_exists_observesQuantity (D : Display) (a : Attachment) :
    Supports D a ↔ ∃ r, ObservesQuantity D univ r a.target := by
  cases a
  · simp [Supports, ObservesQuantity, OverDescribes, Attachment.target, Description.bareOf,
      Description.kind]
  simp only [Supports, ObservesQuantity, OverDescribes, Attachment.target, Description.bareOf,
    Description.kind, ne_eq, reduceCtorEq, not_false_eq_true, true_and, forall_const]
  refine ⟨fun ⟨⟨r, hr⟩, h⟩ ↦ ⟨r, hr, fun h' ↦ h ⟨r, h'.2⟩⟩,
    fun ⟨r, hr, hb⟩ ↦ ⟨⟨r, hr⟩, fun ⟨r', hr'⟩ ↦ hb ⟨hr, ?_⟩⟩⟩
  unfold Identifies at hr hr' ⊢
  rw [distinguishes_univ_erase_iff] at hr hr' ⊢
  obtain rfl := (Set.eq_singleton_iff_unique_mem.1 hr').2 r
    (Set.eq_singleton_iff_unique_mem.1 hr).1.1
  exact hr'

/-- The Referential Model takes *on the towel* as the location in the one-referent display and as
a modifier of *the apple* in the two-referent display (pp. 555–556). -/
theorem supports_oneReferent_twoReferent :
    (∀ a, Supports oneReferent a ↔ a = .location) ∧
      ∀ a, Supports twoReferent a ↔ a = .modifier := by
  decide

end EngelhardtEtAl2006
