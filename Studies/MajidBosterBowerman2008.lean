module

public import Linglib.Fragments.English.Verbs.Inventory

/-!
# Majid, Boster and Bowerman (2008): The Cross-Linguistic Categorization of Everyday Events

This file formalizes the stimulus clips of Majid, Boster and Bowerman and the English
descriptions they report. Speakers of twenty-eight languages described sixty-one clips of
separation events, and a correspondence analysis of which clips shared a verb found four
dimensions across the forty-three agentive cutting-and-breaking clips: the predictability of
the locus of separation, tearing, snapping against smashing, and poking a hole. A clip is
described by what the paper states about it, as a region of the substrate's `Root.Content`.

## Main definitions

* `stimulus`: the instrument, object dimensionality and result the paper states for a clip
* `tearing`, `pullingYarn`, `snapping`, `smashing`: the clips named for Dimensions 2 and 3

## Implementation notes

Clips are the appendix numbers. A dimension the paper leaves unstated is unconstrained, so a
root is compatible with a clip (`Root.Content.Overlaps`) when its regions contain the stated
values. The paper classes rope as one-dimensional but not yarn, which is coded like rope.
Positions on the first dimension enter only through the order the text states.

## TODO

The per-language naming data are not in the paper. Its illustrations need fragments with
separation roots: the placement of the karate chop by Chontal, Hindi and Jalonke, and the
Yélî Dnye tearing verb's extension to carrots split along the grain (§3.1). The English
fragment lacks the change-of-state *snap* (its *snap* is the manner-of-speaking verb) and the
*smash*, *stab* and *bodge* the paper reports.

## References

* [majid-boster-bowerman-2008]
-/

@[expose] public section

namespace MajidBosterBowerman2008

open ArgumentStructure.Root ArgumentStructure.Root.Content English English.Verbs

/-! ### Clips -/

/-- In the tearing clips cloth is torn by hand, completely (clip 1) or halfway (clip 36).
Dimension 2 sets them apart from all other clips (§3.1). -/
def tearing : Finset ℕ := {1, 36}

/-- In clips 35 and 38 yarn is pulled apart, and English, German and Dutch extend their
tearing verb to them (§3.1). -/
def pullingYarn : Finset ℕ := {35, 38}

/-- In the snapping clips (25, 19, 57, 5) pressure on both ends separates a one-dimensional
rigid object into two pieces. They form one pole of Dimension 3 (§3.1). -/
def snapping : Finset ℕ := {25, 19, 57, 5}

/-- In the smashing clips (40, 39, 21, 31) a blow fragments a rigid object into many pieces.
They form the other pole of Dimension 3 (§3.1). -/
def smashing : Finset ℕ := {40, 39, 21, 31}

/-- `stimulus c` is what the paper states about clip `c`, as a region of root content. The
hands tear cloth, pull yarn apart and snap one-dimensional objects, a hammer fragments the
smashed objects, and clips 10 and 32 cut a carrot, one of the paper's one-dimensional objects
(§2.2), with a knife and with a karate chop. -/
def stimulus (c : ℕ) : Content :=
  if c ∈ tearing then
    { instrument := {.hands}, resultGeometry := {.separation}, patientDimensionality := {.twoD} }
  else if c ∈ pullingYarn then
    { instrument := {.hands}, resultGeometry := {.separation}, patientDimensionality := {.oneD} }
  else if c ∈ snapping then
    { instrument := {.hands}, resultGeometry := {.fracture}, patientDimensionality := {.oneD} }
  else if c ∈ smashing then
    { instrument := {.bluntImpact}, resultGeometry := {.fragmentation} }
  else if c = 10 then { instrument := {.sharpBlade}, patientDimensionality := {.oneD} }
  else if c = 32 then { instrument := {.hands}, patientDimensionality := {.oneD} }
  else {}

/-! ### The first dimension -/

/-- Placement on Dimension 1 is a function neither of the instrument nor of the object (§3.1). -/
theorem dim1_not_factorsThrough {P : Type*} [Preorder P] (pos : ℕ → P)
    (h₁ : pos 10 < pos 32) (h₂ : pos 32 < pos 19) :
    ¬ pos.FactorsThrough (fun c ↦ (stimulus c).instrument) ∧
      ¬ pos.FactorsThrough (fun c ↦ (stimulus c).patientDimensionality) :=
  ⟨fun h ↦ h₂.ne (h (by decide)), fun h ↦ h₁.ne (h (by decide))⟩

/-! ### English -/

/-- The fragment's *tear* is compatible with the tearing and yarn-pulling clips (§3.1, Dimension 2).
-/
theorem tear_overlaps_stimulus :
    ∀ c ∈ tearing ∪ pullingYarn, tear_.root.content.Overlaps (stimulus c) := by
  decide

/-- The fragment's *cut* and *break* reject the tearing clips (§3.1). -/
theorem not_cut_not_break_of_tearing : ∀ c ∈ tearing,
    ¬ cut.root.content.Overlaps (stimulus c) ∧ ¬ break_.root.content.Overlaps (stimulus c) := by
  decide

/-- The fragment's *break* is compatible with the snapping and smashing clips (§3.1, Dimension 3;
§3.1.1). -/
theorem break_overlaps_stimulus :
    ∀ c ∈ snapping ∪ smashing, break_.root.content.Overlaps (stimulus c) := by
  decide

end MajidBosterBowerman2008
