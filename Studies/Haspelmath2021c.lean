/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Fragments.Romance.Italian.Pronouns
public import Linglib.Morphology.Morph
public import Linglib.Morphology.Word.Comparative

/-!
# Haspelmath (2021): Bound forms, welded forms, and affixes: Basic concepts for morphological comparison

Haspelmath defines an affix as a bound morph that is not a root, that must occur on a root, and
that cannot occur on roots of different root classes, where a bound form occurs on a root when
it is next to the root or next to an affix that occurs on the root. Roots are the morphs
denoting a thing, an action or a property. The definition is
`Morphology.Comparative.Inventory.IsAffix` with the contentful morphs as roots. This file checks it
against the paper's examples and shows what its recursion needs: the inductive reading misses
affixes that occur only next to other affixes, and when markers separate roots the definition can
have two incompatible solutions.

## Main results

* `latin_affixes`: Latin *-bi*, *-v*, *-s* and *-isti* are affixes, *-s* and *-isti* only
  through *-bi* and *-v*.
* `turkish_affixes`: Turkish *mu* is not an affix, so neither is *-sun*, written as a suffix,
  while *-iyor* is.
* `polish_scie_not_affix`, `english_article_not_affix`, `russian_li_not_affix`: bound forms on
  roots of two classes are not affixes.
* `italian_object_affixes`: the Italian object person forms are affixes on either side of the
  verb, though the Italian fragment records *mi* as a clitic.
* `variableOrder_affixes`: with two suffixes in either order, the least solution has no affix
  and the greatest has both.
* `separated_affixes`: when two markers separate two roots, each marker is an affix in some
  solution but no solution has both.
* `suffixBeforeRoot_not_affix`: occurrence on a root is adjacency on either side, so a suffix
  followed by a root of another class is not an affix.

## Implementation notes

Each example is an inventory of the paper's free forms, each a list of morphs with textbook
attachment labels, together with the classes of its roots. The paper's segmentations are kept,
so Polish *domu* and *zrobili* are single morphs. The welded forms of §5 are not formalized.

## References

* [haspelmath-2021c]
-/

@[expose] public section

namespace Haspelmath2021c

open Morphology Morphology.Comparative

/-! ### Latin (16) -/

/-- The Latin action root *lauda-* 'praise'. -/
def lauda : Morph := .root "lauda"
/-- The Latin second singular suffix *-s*. -/
def s : Morph := .suff "s"
/-- The Latin future suffix *-bi*. -/
def bi : Morph := .suff "bi"
/-- The Latin perfect suffix *-v*. -/
def v : Morph := .suff "v"
/-- The Latin second singular perfect suffix *-isti*. -/
def isti : Morph := .suff "isti"

/-- The Latin free forms of (16), *lauda-s*, *lauda-bi-s* and *lauda-v-isti*. -/
def latin : Inventory Morph where
  forms := [[lauda, s], [lauda, bi, s], [lauda, v, isti]]
  rootClass m := if m = lauda then some .action else none

/-- The four suffixes of (16) are affixes, though with no affixes given only *-bi* and *-v* pass. -/
theorem latin_affixes :
    (∀ m ∈ [bi, v, s, isti], latin.IsAffix latin.IsContentful m) ∧
      latin.AffixStep latin.IsContentful ∅ bi ∧
      ¬ latin.AffixStep latin.IsContentful ∅ s ∧
      ¬ latin.AffixStep latin.IsContentful ∅ isti := by
  decide

/-! ### Turkish (18) -/

/-- The Turkish action root *gel* 'come'. -/
def gel : Morph := .root "gel"
/-- The Turkish progressive suffix *-iyor*. -/
def iyor : Morph := .suff "iyor"
/-- The Turkish second singular *-sun*, written as a suffix. -/
def sun : Morph := .suff "sun"
/-- The Turkish question particle *mu*, written apart. -/
def mu : Morph := .encl "mu"
/-- The Turkish object root *su* 'water'. -/
def su : Morph := .root "su"

/-- The Turkish free forms of (18), *gel-iyor-sun*, *gel-iyor mu-sun* and *su mu*. -/
def turkish : Inventory Morph where
  forms := [[gel, iyor, sun], [gel, iyor, mu, sun], [su, mu]]
  rootClass m :=
    if m = gel then some .action else if m = su then some .object else none

/-- In (18), *-iyor* is an affix, while *mu* and the following *-sun* (18b) are not. -/
theorem turkish_affixes :
    turkish.IsAffix turkish.IsContentful iyor ∧
      ¬ turkish.IsAffix turkish.IsContentful mu ∧
      sun.kind = .bound .after .affix ∧
      ¬ turkish.IsAffix turkish.IsContentful sun := by
  decide

/-! ### Bound forms on roots of two classes (15) -/

/-- The Polish preposition *w* 'in'. -/
def w : Morph := .free "w"
/-- The Polish object form *domu* 'house'. -/
def domu : Morph := .root "domu"
/-- The Polish demonstrative *to* 'that'. -/
def «to» : Morph := .free "to"
/-- The Polish action form *zrobili* 'did'. -/
def zrobili : Morph := .root "zrobili"
/-- The Polish second plural *=ście*. -/
def scie : Morph := .encl "ście"

/-- The Polish free forms of (15), *W domu to zrobili=ście?* and *W domu=ście to zrobili?*. -/
def polish : Inventory Morph where
  forms := [[w, domu, «to», zrobili, scie], [w, domu, scie, «to», zrobili]]
  rootClass m :=
    if m = domu then some .object else if m = zrobili then some .action else none

/-- In (15), *=ście* occurs on a verb and on a noun, so it is not an affix. -/
theorem polish_scie_not_affix : ¬ polish.IsAffix polish.IsContentful scie := by
  decide

/-- The English indefinite article *a*. -/
def a : Morph := .free "a"
/-- The English indefinite article *an*. -/
def an : Morph := .free "an"
/-- The English object root *house*. -/
def house : Morph := .root "house"
/-- The English object root *apple*. -/
def apple : Morph := .root "apple"
/-- The English property root *big*. -/
def big : Morph := .root "big"
/-- The English property root *open*. -/
def «open» : Morph := .root "open"

/-- The English free forms *a house*, *an apple*, *a big house* and *an open house*. -/
def english : Inventory Morph where
  forms := [[a, house], [an, apple], [a, big, house], [an, «open», house]]
  rootClass m :=
    if m = house ∨ m = apple then some .object
    else if m = big ∨ m = «open» then some .property else none

/-- The English indefinite article occurs on nouns and on prenominal adjectives, so neither of
its shapes is a prefix. -/
theorem english_article_not_affix :
    ¬ english.IsAffix english.IsContentful a ∧
      ¬ english.IsAffix english.IsContentful an := by
  decide

/-- The Russian action form *znaeš'* 'you know'. -/
def znaesh : Morph := .root "znaeš'"
/-- The Russian property form *zdorov* 'well'. -/
def zdorov : Morph := .root "zdorov"
/-- The Russian adverb *zdes'* 'here'. -/
def zdes : Morph := .free "zdes'"
/-- The Russian interrogative enclitic *li*. -/
def li : Morph := .encl "li"

/-- The Russian free forms *znaeš' li?*, *zdorov li?* and *zdes' li?*. -/
def russian : Inventory Morph where
  forms := [[znaesh, li], [zdorov, li], [zdes, li]]
  rootClass m :=
    if m = znaesh then some .action else if m = zdorov then some .property else none

/-- *li* occurs on verbs and adjectives, so it is not an affix. -/
theorem russian_li_not_affix :
    ¬ russian.IsAffix russian.IsContentful li := by
  decide

/-! ### Italian (19) -/

/-- The Italian first singular dative *mi*, before the verb. -/
def mi : Morph := .procl Italian.Pronouns.mi.form
/-- The Italian first singular dative *-mmi*, after an imperative. -/
def mmi : Morph := .encl "mmi"
/-- The Italian action root *da* 'give'. -/
def da : Morph := .root "da"

/-- The Italian free forms of (19), *mi da* and *da-mmi*. -/
def italian : Inventory Morph where
  forms := [[mi, da], [da, mmi]]
  rootClass m := if m = da then some .action else none

/-- In (19), the object person forms are affixes, though the Italian fragment records *mi* as a
clitic. -/
theorem italian_object_affixes :
    Italian.Pronouns.mi.strength = some .clitic ∧
      italian.IsAffix italian.IsContentful mi ∧
      italian.IsAffix italian.IsContentful mmi := by
  decide

/-! ### Solutions of the definition -/

/-- The schematic inventories have three roots and two bound morphs. -/
inductive Schematic where
  | y | y₁ | y₂ | x | z
  deriving DecidableEq, Fintype, Repr

open Schematic

/-- The classes of the schematic roots. -/
def schematicClass : Schematic → Option RootClass
  | .y | .y₂ => some .action
  | .y₁ => some .object
  | .x | .z => none

/-- One root with two suffixes in either order. -/
def variableOrder : Inventory Schematic := ⟨[[y, x, z], [y, z, x]], schematicClass⟩

/-- With two suffixes in either order, the empty set solves the definition, so its least
solution has no affix, while both suffixes are affixes, its greatest solution. -/
theorem variableOrder_affixes :
    (∀ m, ¬ variableOrder.AffixStep variableOrder.IsContentful ∅ m) ∧
      {m | variableOrder.IsAffix variableOrder.IsContentful m} = {x, z} ∧
      ∀ f ∈ variableOrder.forms, RootsContiguous variableOrder.IsContentful f := by
  refine ⟨by decide, Set.ext fun m ↦ ?_, by decide⟩
  cases m <;> simp <;> decide

/-- Two roots of different classes separated by two bound morphs, each also next to one root. -/
def separated : Inventory Schematic := ⟨[[y₁, x, z, y₂], [y₁, x], [z, y₂]], schematicClass⟩

/-- When two markers separate two roots, each marker is an affix in some solution of the
definition, but given that both are affixes, neither passes. -/
theorem separated_affixes :
    separated.IsAffix separated.IsContentful x ∧
      separated.IsAffix separated.IsContentful z ∧
      ¬ separated.AffixStep separated.IsContentful {m | m = x ∨ m = z} x ∧
      ¬ separated.AffixStep separated.IsContentful {m | m = x ∨ m = z} z := by
  decide

/-- A suffix that always follows an object root, followed in a longer free form by an action
root. -/
def suffixBeforeRoot : Inventory Schematic := ⟨[[y₁, x], [y₁, x, y₂]], schematicClass⟩

/-- Occurrence on a root is adjacency on either side, so a suffix that always follows an object
root but precedes an action root in a longer free form occurs on roots of two classes, and is
not an affix. -/
theorem suffixBeforeRoot_not_affix :
    ¬ suffixBeforeRoot.IsAffix suffixBeforeRoot.IsContentful x := by
  decide

end Haspelmath2021c
