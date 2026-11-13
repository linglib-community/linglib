module

public import Linglib.Data.Examples.EngelhardtEtAl2006
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Statistics.EngelhardtEtAl2006
public import Linglib.Fragments.English.Adpositions
public import Linglib.Semantics.Reference.Description
public import Linglib.Semantics.Reference.ReferentialSupport
public import Linglib.Syntax.Case.Spatial
public import Mathlib.Data.Fin.VecNotation

/-!
# Engelhardt et al. (2006): Do Speakers and Listeners Observe the Gricean Maxim of Quantity?

This file formalizes the maxim of Quantity for the definite descriptions in Engelhardt, Bailey and
Ferreira's instructions. A description under-describes an object when *the* with it does not pick
the object out, and over-describes it when it has a modifier its bare noun does not need. Speakers
[over-describe but do not under-describe](##speakers_overDescribe), and listeners [rate only the
under-descriptions significantly lower](##listeners_penalize_underDescription). [*The towel* is
undefined](##identifies_towel) in the display, not among the places the apple can be moved to.
[Referential support is the maxim](##referentiallySupported_iff_exists_observesQuantity), so with
one apple it [takes *on the towel* as the destination](##supports_oneReferent_iff).

## Implementation notes

* *The towel* in *on the towel* is read as some towel, since every display has two.
* The fixations of Experiment 3 are not formalized.

## References

* [engelhardt-etal-2006]
* [grice-1975]
* [schwarz-2009]
* [altmann-steedman-1988]
-/

@[expose] public section

namespace EngelhardtEtAl2006

open EngelhardtEtAl2006.Examples Finset

/-- The category labels of the objects, the apple to be moved, the frog, and the two kinds of
destination. -/
inductive Kind
  | apple
  | frog
  | towel
  | box
  deriving DecidableEq

/-- An object of a display. -/
structure Object where
  /-- The category label of the object. -/
  kind : Kind
  /-- The object it is located on or in, if any, with the part of it the object is localized in. -/
  ground : Option (Spatial.Localization × Fin 5)

/-- A display of five objects, the target first. -/
abbrev Display := Fin 5 → Object

/-- The one-referent display, an apple on a towel, a frog, an empty towel and an empty box. -/
def oneReferent : Display :=
  ![⟨.apple, some (.surface, 1)⟩, ⟨.towel, none⟩, ⟨.frog, none⟩, ⟨.towel, none⟩, ⟨.box, none⟩]

/-- The two-referent display, with a second apple by itself for the frog. -/
def twoReferent : Display := Function.update oneReferent 2 ⟨.apple, none⟩

/-- The objects the target can be moved to: all but the target and the object it is on. -/
def destinations (D : Display) : Finset (Fin 5) :=
  {i | i ≠ 0 ∧ (D 0).ground.map Prod.snd ≠ some i}

/-! ### Descriptions and the maxim -/

/-- A modifier in the descriptions, a prepositional phrase locating the referent on or in an
object of a kind, or *other*, which excludes the object the target is on. -/
inductive NounModifier
  | pp (p : Adposition) (k : Kind)
  | other
  deriving DecidableEq

/-- The property an intersective modifier meets its noun with: for a prepositional phrase, being
located in a part of an object of the kind that the preposition marks as a place. -/
def NounModifier.property (D : Display) : NounModifier → Fin 5 → Prop
  | .pp p k, i => ∃ ℓ j, (ℓ, j) ∈ (D i).ground ∧ (ℓ, .place) ∈ Case.cells p.functions ∧
      (D j).kind = k
  | .other, i => (D 0).ground.map Prod.snd ≠ some i

instance (D : Display) (m : NounModifier) : DecidablePred (m.property D) := fun i ↦ by
  cases m <;> unfold NounModifier.property <;> infer_instance

/-- A description in the instructions, a noun with a modifier, if any. -/
structure Description where
  /-- The head noun. -/
  noun : Kind
  /-- The modifier. -/
  modifier : Option NounModifier
  deriving DecidableEq

/-- The bare noun of a description. -/
def Description.bare (d : Description) : Description := ⟨d.noun, none⟩

/-- The property a description denotes, its noun's met by its modifier's. -/
def Description.property (D : Display) (d : Description) : Fin 5 → Prop :=
  d.modifier.elim (fun i ↦ (D i).kind = d.noun) fun m ↦
    Modifier.intersective (m.property D) fun i ↦ (D i).kind = d.noun

instance (D : Display) (d : Description) : DecidablePred (d.property D) := fun i ↦ by
  rcases d with ⟨k, _ | m⟩
  · exact inferInstanceAs (Decidable ((D i).kind = k))
  · exact inferInstanceAs (Decidable (m.property D i ∧ (D i).kind = k))

/-- The restrictor of *the* with a description, which holds of the objects of the resource
situation that the description does. -/
def Description.restrictor (D : Display) (d : Description) :
    (ℕ → Fin 5) → Finset (Fin 5) → Set (Fin 5) :=
  fun _ s ↦ {i | i ∈ s ∧ d.property D i}

instance (D : Display) (d : Description) (g : ℕ → Fin 5) (s : Finset (Fin 5)) :
    DecidablePred (· ∈ d.restrictor D g s) := fun i ↦
  inferInstanceAs (Decidable (i ∈ s ∧ d.property D i))

section Maxim

variable (D : Display) (s : Finset (Fin 5)) (r : Fin 5) (d : Description)

/-- *The* with the description, the weak article of [schwarz-2009], picks out `r` in the resource
situation `s`. -/
def Identifies : Prop := r ∈ Definite.unique (d.restrictor D) default s

instance : Decidable (Identifies D s r d) :=
  decidable_of_iff _ Definite.mem_unique.symm

/-- The description identifies `r` in `s` with a modifier its bare noun does not need. -/
def OverDescribes : Prop := d.modifier.isSome ∧ Identifies D s r d ∧ Identifies D s r d.bare

instance : Decidable (OverDescribes D s r d) := inferInstanceAs (Decidable (_ ∧ _))

/-- The description observes the maxim of Quantity for `r` in `s`: it identifies `r` without
over-describing it. -/
def ObservesQuantity : Prop := Identifies D s r d ∧ ¬ OverDescribes D s r d

instance : Decidable (ObservesQuantity D s r d) := inferInstanceAs (Decidable (_ ∧ _))

end Maxim

/-- *The towel* is undefined in the display but picks out the empty towel among the objects the
apple can be moved to (pp. 561, 569). -/
theorem identifies_towel :
    ∀ D ∈ [oneReferent, twoReferent],
      ¬ Identifies D univ 3 ⟨.towel, none⟩ ∧ Identifies D (destinations D) 3 ⟨.towel, none⟩ := by
  decide

/-! ### The instructions -/

/-- An instruction, *Put the apple … in/on the …*. -/
structure Instruction where
  /-- The description of the object to be moved. -/
  target : Description
  /-- The description of the object it is to be moved to. -/
  destination : Description
  deriving DecidableEq

/-- The target description of an instruction type, *the apple* or *the apple on the towel*. -/
def InstructionType.target : InstructionType → Description
  | .bare => ⟨.apple, none⟩
  | .modified => ⟨.apple, some (.pp English.Adpositions.on .towel)⟩

/-- The target descriptions as named in the rows. -/
def targetTable : List (String × Description) :=
  [("bare", InstructionType.bare.target), ("modified", InstructionType.modified.target)]

/-- The destination descriptions as named in the rows. -/
def destinationTable : List (String × Description) :=
  [("towel", ⟨.towel, none⟩), ("otherTowel", ⟨.towel, some .other⟩), ("box", ⟨.box, none⟩)]

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
  instructions.map fun ins ↦ if ins.destination = ⟨.towel, none⟩ then
    { ins with destination := ⟨.towel, some .other⟩ } else ins

/-- The object an instruction moves the target to in either display, the empty towel or the
box. -/
def Instruction.goal (ins : Instruction) : Fin 5 := if ins.destination.noun = .towel then 3 else 4

/-- An instruction observes the maxim of Quantity in a display when its target and destination
descriptions do in the whole display. -/
def Instruction.ObservesQuantity (D : Display) (ins : Instruction) : Prop :=
  EngelhardtEtAl2006.ObservesQuantity D univ 0 ins.target ∧
    EngelhardtEtAl2006.ObservesQuantity D univ ins.goal ins.destination

instance (D : Display) (ins : Instruction) : Decidable (ins.ObservesQuantity D) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- Table 1, p. 561
theorem observesQuantity_instructions :
    ∀ ins ∈ instructions,
      (ins.ObservesQuantity oneReferent ↔ ins = ⟨⟨.apple, none⟩, ⟨.box, none⟩⟩) ∧
        (ins.ObservesQuantity twoReferent ↔ ins.target.modifier.isSome) := by
  decide

-- p. 564
theorem observesQuantity_instructions2b :
    ∀ ins ∈ instructions2b,
      Identifies oneReferent univ 0 ins.target ∧
        ObservesQuantity oneReferent univ ins.goal ins.destination ∧
          (OverDescribes oneReferent univ 0 ins.target ↔ ins.target.modifier.isSome) := by
  decide

/-! ### The findings -/

/-- A test finds its effect when it prints p-values below .05 by subjects, by items and for
min F'. -/
def Test.Found (t : Test) : Prop :=
  (∃ p ∈ t.p1, p.Significant (1 / 20)) ∧ (∃ p ∈ t.p2, p.Significant (1 / 20)) ∧
    ∃ p ∈ t.pMin, p.Significant (1 / 20)

instance : DecidablePred Test.Found := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The paper finds an effect in an experiment, in a context type or over both, when it prints a
test of the effect that finds it. -/
def Found (x : Experiment) (e : Effect) (c : Option ContextType) : Prop :=
  ∃ t ∈ tests, t.experiment = x ∧ t.effect = e ∧ t.context = c ∧ t.Found

instance (x : Experiment) (e : Effect) (c : Option ContextType) : Decidable (Found x e c) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- A comparison's difference of Experiment 2's mean ratings exceeds its confidence interval. -/
def Comparison.Exceeds (c : Comparison) : Prop :=
  (exp2Ratings c.lowerInstruction c.lowerLocation).mean.toRat + c.interval.toRat <
    (exp2Ratings c.higherInstruction c.higherLocation).mean.toRat

instance (c : Comparison) : Decidable c.Exceeds := inferInstanceAs (Decidable (_ < _))

/-- The modified target over-describes the apple in the one-referent display, and Experiment 1's
speakers produced it on 30% of the trials there, significantly more than none; the bare target
under-describes the apple in the two-referent display, where they produced the modified target
significantly more often, on 98% (p. 560). -/
theorem speakers_overDescribe :
    OverDescribes oneReferent univ 0 InstructionType.modified.target ∧
      0 < (production .oneReferent).modifiedTarget.toRat ∧
      Found .exp1 .aboveZero (some .oneReferent) ∧
      ¬ Identifies twoReferent univ 0 InstructionType.bare.target ∧
      (production .oneReferent).modifiedTarget.toRat <
        (production .twoReferent).modifiedTarget.toRat ∧
      Found .exp1 .context none := by
  decide +kernel

/-- Experiment 2's listeners rated the bare target, which under-describes the apple in the
two-referent display, significantly below the modified one there; Experiment 2b's listeners rated
each instruction whose target over-describes the apple in the one-referent display below the
instruction with the bare target and the same location type, but not significantly (pp. 563–564,
Table 4). -/
theorem listeners_penalize_underDescription :
    ¬ Identifies twoReferent univ 0 InstructionType.bare.target ∧
      (exp2TwoReferentRatings .bare).mean.toRat < (exp2TwoReferentRatings .modified).mean.toRat ∧
      Found .exp2 .instruction (some .twoReferent) ∧
      (∀ ins ∈ instructions2b, ¬ ins.ObservesQuantity oneReferent ↔
        OverDescribes oneReferent univ 0 ins.target) ∧
      (∀ l, (exp2bRatings .modified l).mean.toRat < (exp2bRatings .bare l).mean.toRat) ∧
      ¬ Found .exp2b .instruction (some .oneReferent) := by
  decide +kernel

-- p. 563
theorem overDescribes_rated_lower_exp2 :
    OverDescribes oneReferent univ 0 InstructionType.modified.target ∧
      ∃ c ∈ comparisons, c.higherInstruction = .bare ∧ c.higherLocation = .different ∧
        c.lowerInstruction = .modified ∧ c.lowerLocation = .different ∧ c.Exceeds := by
  decide +kernel

/-! ### The Referential Model -/

/-- The definite with a description is referentially supported in the display exactly when the
description observes the maxim of Quantity for some object. -/
theorem referentiallySupported_iff_exists_observesQuantity (D : Display) (d : Description) :
    ReferentiallySupported {i | d.bare.property D i}
      (d.modifier.map fun m ↦ {i | m.property D i}) ↔
      ∃ r, ObservesQuantity D univ r d := by
  have h (d : Description) (r : Fin 5) :
      Identifies D univ r d ↔ r ∈ iota {i | d.property D i} := by
    unfold Identifies Description.restrictor
    simp
  rcases d with ⟨k, _ | m⟩
  · simp [ObservesQuantity, OverDescribes, h, Description.bare, Part.dom_iff_mem]
  · simp only [referentiallySupported_some_iff, ObservesQuantity, OverDescribes, h,
      Description.bare, Option.isSome_some, true_and, Option.map_some]
    exact exists_congr fun _ ↦ and_congr_right fun ha ↦
      ⟨fun hb h ↦ hb h.2, fun h hb ↦ h ⟨ha, hb⟩⟩

/-- The two analyses of *on the towel* in *put the apple on the towel …*, as the location the apple
is to be put, or as a modifier of *the apple*. -/
inductive Attachment
  | location
  | modifier
  deriving DecidableEq, Fintype

/-- The description of the target under an analysis. -/
def Attachment.target : Attachment → Description
  | .location => InstructionType.bare.target
  | .modifier => InstructionType.modified.target

/-- The Referential Model takes *on the towel* as the location in the one-referent display
(pp. 555–556). -/
theorem supports_oneReferent_iff {a : Attachment} :
    ReferentiallySupported {i | a.target.bare.property oneReferent i}
        (a.target.modifier.map fun m ↦ {i | m.property oneReferent i}) ↔ a = .location := by
  rw [referentiallySupported_iff_exists_observesQuantity]
  revert a; decide

theorem supports_twoReferent_iff {a : Attachment} :
    ReferentiallySupported {i | a.target.bare.property twoReferent i}
        (a.target.modifier.map fun m ↦ {i | m.property twoReferent i}) ↔ a = .modifier := by
  rw [referentiallySupported_iff_exists_observesQuantity]
  revert a; decide

end EngelhardtEtAl2006
