module

public import Linglib.Morphology.Exponence.Containment.Contiguity
public import Studies.Haspelmath1997
public import Linglib.Data.Examples.Dekier2021
public import Linglib.Data.Examples.Readers

/-!
# Dekier (2021): Morphosyntax of specific and non-specific indefinite markers

This file formalizes Dekier's nanosyntactic analysis of the markers of the non-specific,
specific unknown and specific known functions of Haspelmath's map. Across a sample of 45
languages the three markers show the syncretism patterns AAA, ABB, AAB and ABC and never ABA,
Table 7, the generalization of Bobaljik, so they spell out a hierarchy of structural
containment, (4): the non-specific layer inside the specific unknown one inside the specific
known one, the direction fixed by functional complexity, (37). A language's lexicon stores for
each marker the largest layer it spells out; the Superset Principle of Starke and Caha, (42),
lets an entry spell out any layer it contains and the Elsewhere Principle, (47), picks the
smallest match, so the lexicon read off the coverage Haspelmath draws for each paradigm
reproduces that coverage by spellout, the absence of
ABA is the contiguity of spellout, (48), and a paradigm gap, Table 6, sits above every filled
layer, since an entry spelling out a layer spells out every layer below it. An interrogative pronoun
can be spelled out as a subset of an indefinite entry, (78) and (79), and suffixes arise by
spellout-driven movement where prefixes arise by subderivation, (57).

## Implementation notes

Layers are the grades `Fin 3` of the containment substrate and entries its context-free span
rules, with `spellout` the exponent of the Superset-and-Elsewhere winner. The paradigms are
those of `Studies/Haspelmath1997.lean`, a series covering a layer when the layer's function lies
in the region the book draws for it. A layer's form is the marker of the one series covering its
function, `none` at a gap or where series overlap. The markers are named as the book names them,
which departs from the paper's notation in places (*-nibud'* against *-nibud*, *kaut* against
*kaut-*), so the theorems over them compare coverage patterns and the paper's marker tables are
rows. The paper's Russian row has the three series that divide the hierarchy and not
*-libo*, which the book draws over the non-specific function beside *-nibud'*; the book draws
*-to* over that function too, so Russian's coverage has no single non-specific form and its
ABC pattern is the work of the Elsewhere Principle (`russian_elsewhere`). The derivations of
prefixes and suffixes in §4.2 are not modelled.

## References

* [dekier-2021]
* [haspelmath-1997]
* [bobaljik-2012]
* [starke-2009]
* [caha-2009]
-/

@[expose] public section

namespace Dekier2021

open Morphology Morphology.Exponence Morphology.Containment Indefinite Haspelmath1997

/-! ### The hierarchy -/

/-- `layer` sends a specificity function to the layer of the hierarchy (4) its marker spells
out, the non-specific function to the lowest and the specific known to the highest. -/
def layer : SpecificityFunction ≃ Fin 3 where
  toFun
    | .nonSpecific => 0
    | .specificUnknown => 1
    | .specificKnown => 2
  invFun := ![.nonSpecific, .specificUnknown, .specificKnown]
  left_inv := by decide
  right_inv := by decide

/-- The function of the map each layer spells out. -/
def function (g : Fin 3) : HaspelmathFunction := (layer.symm g).toFunction

/-- The form of a paradigm at a function is the form of the one series covering it, and `none`
at a gap or where series overlap. -/
def formAt (p : List Series) (f : HaspelmathFunction) : Option String :=
  match p.filter (f ∈ ·.functions) with
  | [e] => some e.name
  | _ => none

/-- A paradigm's forms over the three layers, the triple the syncretism patterns classify. -/
def pattern (p : List Series) : Paradigm 3 (Option String) :=
  fun g ↦ formAt p (function g)

/-- The layers a series covers. -/
def layers (e : Series) : Finset (Fin 3) :=
  Finset.univ.filter (function · ∈ e.functions)

/-- In the nanosyntactic lexicon of a paradigm each form stores the largest layer it covers, the
Superset and Elsewhere Principles deriving the rest of its coverage. -/
def lexicon (p : List Series) : RuleSet (SupersetRule 3 String) :=
  p.filterMap fun e ↦ (layers e).max.map (⟨e.name, ·⟩)

/-- The Russian series of the paper's row are *koe-*, *-to* and *-nibud'*. -/
def russian : List Series :=
  Haspelmath1997.russian.filter fun e ↦
    e.toSeries ∈ [Russian.Indefinites.koeSeries, Russian.Indefinites.toSeries,
      Russian.Indefinites.nibudSeries]

/-! ### Syncretism and its absence -/

-- Table 1
theorem map_syncretism :
    Setoid.ker (pattern english) = Setoid.ker Paradigm.aaa ∧
      Setoid.ker (pattern yakut) = Setoid.ker Paradigm.abb ∧
      Setoid.ker (pattern latin) = Setoid.ker Paradigm.aab := by
  decide

theorem russian_elsewhere :
    pattern russian 0 = none ∧
      spellout (lexicon russian) = ![some "-nibud'", some "-to", some "koe-"] ∧
      Setoid.ker (spellout (lexicon russian)) = Setoid.ker Paradigm.abc := by
  decide

theorem kannada_gap : pattern kannada 2 = none := by decide

-- (59), (67), (70)
theorem spellout_lexicon :
    ∀ p ∈ [english, yakut, latin, kannada], spellout (lexicon p) = pattern p := by
  decide

-- (48)
theorem not_aba {v : RuleSet (SupersetRule 3 String)} (hv : v.Antihomophonous)
    (h : spellout v 0 = spellout v 2) : spellout v 0 = spellout v 1 :=
  isContiguous_spellout hv (by decide) (by decide) h

-- §6.3
theorem ne_none_of_le {v : RuleSet (SupersetRule 3 String)} {g g' : Fin 3} (h : g ≤ g')
    (hg' : spellout v g' ≠ none) : spellout v g ≠ none :=
  fun hg ↦ hg' (spellout_eq_none_of_le hg h)

-- (78), (79)
theorem interrogative_subset :
    spellout [(⟨"shénme", 1⟩ : SupersetRule 4 String)] =
        ![some "shénme", some "shénme", none, none] ∧
      spellout [(⟨"wat", 3⟩ : SupersetRule 4 String)] = fun _ ↦ some "wat" := by
  decide

/-! ### The sample -/

/-- A row's markers over the three layers, a gap read as `none`. -/
def rowPattern (e : Datum) : Paradigm 3 (Option String) :=
  ![e.feature? "nonSpecific", e.feature? "specificUnknown", e.feature? "specificKnown"]

-- Table 7
theorem rows_contiguous : ∀ e ∈ Examples.all, IsContiguous (rowPattern e) := by
  decide

-- Table 6
theorem rows_gap_above : ∀ e ∈ Examples.all, ∀ g g' : Fin 3, g ≤ g' →
    rowPattern e g' ≠ none → rowPattern e g ≠ none := by
  decide

end Dekier2021
