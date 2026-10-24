module

public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Fragments.Romance.Spanish.Verbs

/-!
# Spalek & McNally (2026): The Anatomy of a Verb

This file formalizes the contrastive analysis of English *tear* and Spanish *rasgar* of Spalek and
McNally. The two verbs are counterparts in comparative lexical databases and share an event
structure: both are simple result verbs of Levin's break class describing a minimal, binary-scale
change, the partly uncontrolled loss of integrity of a whole, with a causative alternation and no
agentive intransitive use. They differ in root content, the fine within-class half of a root's
meaning beside its templatic kinds in the sense of Beavers and Koontz-Garboden: *rasgar* requires a
flimsy or insubstantial patient and implies a linear, gash-like separation without much force, where
*tear* takes patients of any robustness, implies separation in contrary directions, often with
force, and is compatible with careful action. Figurative extensions follow the root content, the
case complementary to the event-structural contrasts of McNally and Spalek's 2022 paper: *rasgar*
disturbs fragile states, silence and darkness, and describes linear movement through an
insubstantial medium; *tear* rends with force and describes fast motion along a path. In the
bidirectional parallel corpus the verbs are asymmetric translation equivalents: *rasgar* is one of
the rarer renderings of *tear*, whose most frequent counterpart is *arrancar*, while *tear* is the
usual rendering of *rasgar*.

The root contents are the fragment entries' `root.content`, regions of the substrate's
`Root.Content` space, and the paper's examples are points of it, `Root.Content.Situation`s, a
described event's value on every dimension. A root admits a situation when the situation lies
in its region, and the substrate's `overlaps_iff_exists_mem` identifies `Overlaps` with the
existence of a situation both roots admit, the zone in which the verbs are intertranslatable.
The paper's contrasts are situations one root admits and the other rejects: the chunk of bread
(14), the engraved cement (16b), the carefully torn foil (17), the rooster and the silence (18),
and the ball tearing through the rough (23); the soft contact lenses (16a) are admitted by both.

## Implementation notes

The translation counts of the paper's Tables 1 and 2 are reported in prose. Each contrast
situation is fixed on the dimension the paper names for it and agrees with the contact
lenses elsewhere, inside both roots' regions, so that each verdict turns on the named
dimension alone: robustness for the bread, result geometry for the cement, agent control
for the foil, robustness and force for the silence, force for the rough.

## References

* [spalek-mcnally-2026]
* [mcnally-spalek-2022]
* [beavers-koontz-garboden-2020]
* [levin-1993]
-/

@[expose] public section

namespace SpalekMcNally2026

open ArgumentStructure.Root ArgumentStructure.Root.Content English Spanish.Verbs English.Verbs

/-! ### The paper's situations -/

/-- Tearing soft contact lenses with one's nails (16a) separates a flimsy patient by a moderate,
linear force. -/
def lenses : Situation :=
  ⟨.moderate, .unidirectional, .hands, .neutral, .separation, .flimsy, .twoD⟩

/-- Tearing a chunk off a slice of bread (14) has a robust patient. -/
def bread : Situation := { lenses with patientRobustness := .robust }

/-- An awl engraving cement (16b) makes a gash on a surface, with no separation in contrary
directions. -/
def cement : Situation := { lenses with resultGeometry := .surfaceBreach }

/-- Children carefully tearing tin foil (17) control the action. -/
def foil : Situation := { lenses with agentControl := .compatible }

/-- A rooster tearing the silence of the dawn (18) disturbs a fragile state with the least
force. -/
def silence : Situation := { lenses with force := .low, patientRobustness := .insubstantial }

/-- A ball tearing through the rough (23) moves with considerable energy. -/
def rough : Situation := { lenses with force := .high }

theorem lenses_admitted : lenses ∈ tear_.root.content ∧ lenses ∈ rasgar.root.content := by
  decide

theorem roots_overlap : tear_.root.content.Overlaps rasgar.root.content :=
  overlaps_iff_exists_mem.2 ⟨lenses, lenses_admitted⟩

theorem bread_contrast : bread ∈ tear_.root.content ∧ bread ∉ rasgar.root.content := by
  decide

theorem cement_contrast : cement ∉ tear_.root.content ∧ cement ∈ rasgar.root.content := by
  decide

theorem foil_contrast : foil ∈ tear_.root.content ∧ foil ∉ rasgar.root.content := by
  decide

theorem silence_contrast : silence ∉ tear_.root.content ∧ silence ∈ rasgar.root.content := by
  decide

theorem rough_contrast : rough ∈ tear_.root.content ∧ rough ∉ rasgar.root.content := by
  decide

end SpalekMcNally2026
