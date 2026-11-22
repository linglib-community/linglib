module

public import Linglib.Fragments.Finnish.Morphotactics
public import Linglib.Fragments.Turkish.Morphotactics
public import Linglib.Morphology.Morphotactics.AffixTemplate.Scale
public import Mathlib.Tactic.DeriveFintype

/-!
# Bickel and Nichols 2007: templatic morphology and affix order

[bickel-nichols-2007] contrast layered strings of formatives, in which order follows scope, with
templatic ones, in which a formative's position is assigned on formal grounds: two formatives
share a position when they cannot co-occur. Their example is the agreement of the Belhare
intransitive verb, with two prefix positions and five suffix positions. `template` is that
template over the positions `Slot`, and `Exponent` lists the fillers of each.

The third person nonsingular *N-* and the negative *N-* fill the same position, so no form has
both (`not_licensed_of_count_pf2`), and a third person nonsingular negative takes the other
third person prefix, *mi-*. The negative prefix occurs only with the negative suffix, three
positions away. That dependency is not a property of the template, whose strings are closed
under dropping a filler: `licensed_without_negative_suffix`.

They also give orders that formatives tend to keep whether templatic or layered. For nouns it
is number inside case, after [greenberg-1963]; the nominal templates of Turkish and Finnish
ascend along it (`turkish_suffixesAscend`, `finnish_suffixesAscend`).

## TODO

The order given for verbs, voice and aspect inside modality inside status and tense inside
evidentials and illocutionary force, is not formalized: the Belhare positions are not assigned
categories of that scale in the source.

## References

* [bickel-nichols-2007]
* [greenberg-1963]
-/

@[expose] public section

namespace BickelNichols2007

open Morphology

/-! ### The Belhare template -/

/-- Table 3.14: the affix positions of the Belhare intransitive verb, two before the stem and
five after it. -/
inductive Slot where
  | pf1 | pf2 | sf1 | sf2 | sf3 | sf4 | sf5
  deriving DecidableEq, Repr, Fintype

/-- Table 3.14: the fillers of each position. -/
inductive Exponent : Slot → Type where
  /-- *mi-*, third person nonsingular. -/
  | mi : Exponent .pf1
  /-- *N-*, third person nonsingular. -/
  | thirdNonsingular : Exponent .pf2
  /-- *N-*, negative. -/
  | negativePrefix : Exponent .pf2
  /-- *-yuk*, definitive. -/
  | definitive : Exponent .sf1
  /-- *-yakt*, imperfective. -/
  | imperfective : Exponent .sf1
  /-- *-(h)e* or *-att*, past. -/
  | past : Exponent .sf2
  /-- *-t* or *-yuk*, nonpast. -/
  | nonpast : Exponent .sf2
  /-- *-a*, subjunctive. -/
  | subjunctive : Exponent .sf2
  /-- *-chi*, dual. -/
  | dual : Exponent .sf3
  /-- *-i*, first or second person plural. -/
  | participantPlural : Exponent .sf3
  /-- *-n(i)*, negative. -/
  | negativeSuffix : Exponent .sf4
  /-- *-ŋ(a)*, exclusive. -/
  | exclusive : Exponent .sf5
  /-- *-k(a(k))*, second person. -/
  | second : Exponent .sf5
  deriving DecidableEq

/-- Table 3.14: the template of the Belhare intransitive verb. -/
def template : AffixTemplate Slot where
  prefixSlots := [.pf1, .pf2]
  suffixSlots := [.sf1, .sf2, .sf3, .sf4, .sf5]

/-- A string of Belhare formatives, without the stem. -/
abbrev Form := List (Σ σ, Exponent σ)

/-- (57a): *mi-n-ta-at-ni* 'they didn't come'. -/
def theyDidNotCome : Form := [⟨_, .mi⟩, ⟨_, .negativePrefix⟩, ⟨_, .past⟩, ⟨_, .negativeSuffix⟩]

/-- (57b): *n-ta-he* 'they came'. -/
def theyCame : Form := [⟨_, .thirdNonsingular⟩, ⟨_, .past⟩]

/-- (57c): *n-ta-at-ni* 's/he didn't come'. -/
def didNotCome : Form := [⟨_, .negativePrefix⟩, ⟨_, .past⟩, ⟨_, .negativeSuffix⟩]

/-- *n-ta-at-chi-n* 'we two didn't come'. -/
def weTwoDidNotCome : Form :=
  [⟨_, .negativePrefix⟩, ⟨_, .past⟩, ⟨_, .dual⟩, ⟨_, .negativeSuffix⟩]

theorem licensed_examples :
    ∀ w ∈ [theyDidNotCome, theyCame, didNotCome, weTwoDidNotCome], template.Licensed w := by
  decide

/-- No form has two fillers of the second prefix position. -/
theorem not_licensed_of_count_pf2 {w : Form} (h : 1 < (w.map Sigma.fst).count .pf2) :
    ¬ template.Licensed w :=
  fun hw ↦ h.not_ge (AffixTemplate.count_le_one_of_mem_language (by decide) hw)

-- the third person nonsingular *N-* and the negative *N-* do not co-occur
theorem not_licensed_thirdNonsingular_negative :
    ¬ template.Licensed
      ([⟨_, .thirdNonsingular⟩, ⟨_, .negativePrefix⟩, ⟨_, .past⟩, ⟨_, .negativeSuffix⟩] : Form) :=
  not_licensed_of_count_pf2 (by decide)

/-- The template admits the negative prefix without the negative suffix. -/
theorem licensed_without_negative_suffix :
    template.Licensed ([⟨_, .negativePrefix⟩, ⟨_, .past⟩] : Form) :=
  AffixTemplate.isSublistClosed_language (w := didNotCome.map Sigma.fst)
    (by decide) (by decide)

/-! ### Number inside case -/

/-- (59b): the categories of the order given for nouns, number inside case. -/
inductive NominalScale where
  | number
  | case
  deriving DecidableEq, Repr, Fintype

instance : LinearOrder NominalScale := LinearOrder.lift' NominalScale.ctorIdx (by decide)

/-- The scale category of a Turkish nominal position. -/
def turkishCategory? : Turkish.Nominal.Slot → Option NominalScale
  | .number => some .number
  | .case => some .case
  | .possession => none

/-- The scale category of a Finnish nominal position. -/
def finnishCategory? : Finnish.Nominal.Slot → Option NominalScale
  | .number => some .number
  | .case => some .case
  | .function | .possession | .clitic => none

/-- The Turkish nominal suffixes have number inside case. -/
theorem turkish_suffixesAscend :
    Turkish.Nominal.template.SuffixesAscend turkishCategory? := by decide

/-- The Finnish nominal endings have number inside case. -/
theorem finnish_suffixesAscend :
    Finnish.Nominal.template.SuffixesAscend finnishCategory? := by decide

end BickelNichols2007
