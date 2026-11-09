module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Basic

/-!
# Majid, Boster and Bowerman (2008): The Cross-Linguistic Categorization of Everyday Events

This file formalizes the stimulus clips of Majid, Boster and Bowerman. Speakers of twenty-eight
languages described sixty-one clips of separation events, and a correspondence analysis of which
clips shared a verb found four dimensions across the forty-three agentive cutting-and-breaking
clips: the predictability of the locus of separation, tearing, snapping against smashing, and
poking a hole. A clip is described by what the paper states about it, and [its place on the first
dimension is a function neither of the instrument nor of the object](##dim1_not_factorsThrough).

## Implementation notes

Clips are the appendix numbers. A dimension the paper leaves unstated is `none`. The paper classes
rope as one-dimensional but not yarn, which is coded like rope. Positions on the first dimension
enter only through the order the text states.

## TODO

The per-language naming data are not in the paper. Its illustrations need naming rows: the
placement of the karate chop by Chontal, Hindi and Jalonke, the English verbs (*tear* for the
tearing and yarn-pulling clips, distinct from *cut* and *break*; *snap* and *smash*, or *break*
for both), and the Yélî Dnye tearing verb's extension to carrots split along the grain (§3.1).

## References

* [majid-boster-bowerman-2008]
-/

@[expose] public section

namespace MajidBosterBowerman2008

/-! ### Clips -/

/-- The instrument of a clip (§2.2): the hands, a hammer, or a knife. -/
inductive Instrument where
  | hands
  | hammer
  | knife
  deriving DecidableEq

/-- The dimensionality of the object acted on (§2.2): one-dimensional as rope or a carrot,
two-dimensional as cloth or a plate, three-dimensional as a melon or a pot. -/
inductive Dimensionality where
  | one
  | two
  | three
  deriving DecidableEq

/-- What the paper states about a clip, `none` where it is silent. -/
structure Stimulus where
  instrument : Option Instrument := none
  dimensionality : Option Dimensionality := none
  deriving DecidableEq

/-- In the tearing clips cloth is torn by hand, completely (clip 1) or halfway (clip 36).
Dimension 2 sets them apart from all other clips (§3.1). -/
def tearing : Finset ℕ := {1, 36}

/-- In clips 35 and 38 yarn is pulled apart, and English, German and Dutch extend their
tearing verb to them (§3.1). -/
def pullingYarn : Finset ℕ := {35, 38}

/-- In the snapping clips (25, 19, 57, 5) pressure on both ends separates a one-dimensional
rigid object into two pieces. They form one pole of Dimension 3 (§3.1). -/
def snapping : Finset ℕ := {25, 19, 57, 5}

/-- In the smashing clips (40, 39, 21, 31) a hammer blow fragments a rigid object into many
pieces. They form the other pole of Dimension 3 (§3.1). -/
def smashing : Finset ℕ := {40, 39, 21, 31}

/-- `stimulus c` is what the paper states about clip `c`. The hands tear cloth, pull yarn apart
and snap one-dimensional objects, a hammer fragments the smashed objects, and clips 10 and 32 cut
a carrot, one of the paper's one-dimensional objects (§2.2), with a knife and with a karate
chop. -/
def stimulus (c : ℕ) : Stimulus :=
  if c ∈ tearing then ⟨some .hands, some .two⟩
  else if c ∈ pullingYarn ∨ c ∈ snapping then ⟨some .hands, some .one⟩
  else if c ∈ smashing then ⟨some .hammer, none⟩
  else if c = 10 then ⟨some .knife, some .one⟩
  else if c = 32 then ⟨some .hands, some .one⟩
  else {}

/-! ### The first dimension -/

/-- Placement on Dimension 1 is a function neither of the instrument nor of the object (§3.1). -/
theorem dim1_not_factorsThrough {P : Type*} [Preorder P] (pos : ℕ → P)
    (h₁ : pos 10 < pos 32) (h₂ : pos 32 < pos 19) :
    ¬ pos.FactorsThrough (fun c ↦ (stimulus c).instrument) ∧
      ¬ pos.FactorsThrough (fun c ↦ (stimulus c).dimensionality) :=
  ⟨fun h ↦ h₂.ne (h (by decide)), fun h ↦ h₁.ne (h (by decide))⟩

end MajidBosterBowerman2008
