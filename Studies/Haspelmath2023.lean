/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Morph
public import Linglib.Morphology.Root.Basic
public import Linglib.Morphology.Word.Comparative

/-!
# Haspelmath (2023): Defining the word

Haspelmath defines a word as a free morph, a clitic, or a root or compound possibly augmented
by nonrequired affixes and augmented by required affixes if there are any. A clitic is a bound
morph that is neither a root nor an affix, and a required affix is one that must be present in
a free form unless another affix replaces it. This file checks the definitions,
`Morphology.Comparative.Inventory.IsWord` and its parts, against the paper's examples, and compares
the definition with Bloomfield's minimum free form, which it is meant to correct.

## Main results

* `to_clitic_zu_prefix`: English infinitival *to* is a clitic and German *zu-* a prefix.
* `genitive_clitic_suffix`: English genitive *'s* is a clitic and German *-s* a suffix.
* `alber_required`, `geb_required`: Italian *alber* needs the suffix *-o* or *-i* and German
  *geb* the suffix *-en* or *-t*, so the bare roots are not words.
* `tree_word`: English *tree* has no required affix, so it is a word, though not a free form.
* `bloomfield_too_narrow`, `bloomfield_too_broad`: *tree* and the clitic *to* are words but not
  minimum free forms, and *a tree* is a minimum free form but not a word.
* `wordsAt_affix_words`: the words at `.affix` of the English and Italian forms are words, while
  *a=tree*, one word at `.clitic`, is not.

## Implementation notes

Each example is an inventory of the paper's free forms, each a list of morphs with textbook
attachment labels, with the classes of its roots. The definition of an affix refers to the roots
of Definition 6, which needs a free form with the root as its only contentful morph; on the free
forms the paper cites for Definition 2 these are exactly the contentful morphs
(`roots_contentful`), and the other inventories take the contentful morphs as roots. The English
article's distribution comes from the 2021 paper's *a house*, *a big house*. Compounds are not
formalized.

## References

* [bloomfield-1933]
* [haspelmath-2021c]
* [haspelmath-2023]
-/

@[expose] public section

namespace Haspelmath2023

open Morphology Morphology.Comparative

/-! ### Roots -/

/-- The English possessive *my*. -/
def my : Morph := .procl "my"
/-- The English object root *husband*. -/
def husband : Morph := .root "husband"
/-- The English article *a*. -/
def a : Morph := .procl "a"
/-- The English object root *café*. -/
def cafe : Morph := .root "café"
/-- The English pronoun *he*. -/
def he : Morph := .procl "he"
/-- The English auxiliary *is*. -/
def is : Morph := .free "is"
/-- The English action root *work*. -/
def work : Morph := .root "work"
/-- The English progressive suffix *-ing*. -/
def ing : Morph := .suff "ing"
/-- The English property root *nice*. -/
def nice : Morph := .root "nice"
/-- The English adverb *now*. -/
def now : Morph := .free "now"
/-- The English interjection *ouch*. -/
def ouch : Morph := .free "ouch"

/-- The English free forms cited for Definitions 1 and 2 are *nice*, *work*, *now*, *ouch*,
*my husband*, *a café* and *he is working*. -/
def freeForms : Inventory Morph where
  forms := [[nice], [work], [now], [ouch], [my, husband], [a, cafe], [he, is, work, ing]]
  rootClass m :=
    if m = husband ∨ m = cafe then some .object
    else if m = work then some .action else if m = nice then some .property else none

/-- On these free forms the roots of Definition 6 are the contentful morphs. -/
theorem roots_contentful :
    ∀ m ∈ freeForms.forms.flatten,
      freeForms.IsRoot m ↔ freeForms.IsContentful m := by
  decide

/-! ### Clitics and affixes -/

/-- The English infinitival *to*. -/
def «to» : Morph := .procl "to"
/-- The English action root *destroy*. -/
def destroy : Morph := .root "destroy"
/-- The English property root *thorough*. -/
def thorough : Morph := .root "thorough"
/-- The English adverbial suffix *-ly*. -/
def ly : Morph := .suff "ly"

/-- The English infinitives *to destroy* and *to thoroughly destroy*. -/
def infinitives : Inventory Morph where
  forms := [[«to», destroy], [«to», thorough, ly, destroy]]
  rootClass m :=
    if m = destroy then some .action else if m = thorough then some .property else none

/-- The German particle *aus* 'out'. -/
def aus : Morph := .pref "aus"
/-- The German infinitival *zu-*. -/
def zu : Morph := .pref "zu"
/-- The German action root *geh* 'go'. -/
def geh : Morph := .root "geh"
/-- The German infinitive suffix *-en*. -/
def en : Morph := .suff "en"

/-- The German infinitive *aus-zu-gehen* 'to go out'. -/
def ausZuGehen : Inventory Morph where
  forms := [[aus, zu, geh, en]]
  rootClass m := if m = geh then some .action else none

theorem to_clitic_zu_prefix :
    infinitives.IsClitic infinitives.IsContentful «to» ∧
      ausZuGehen.IsAffix ausZuGehen.IsContentful zu := by
  decide

/-- The English and German object root *Kim*. -/
def kim : Morph := .root "Kim"
/-- The English genitive *'s*. -/
def s_gen : Morph := .encl "s"
/-- The English object root *umbrella*. -/
def umbrella : Morph := .root "umbrella"
/-- The English article *the*. -/
def the : Morph := .procl "the"
/-- The English object root *dog*. -/
def dog : Morph := .root "dog"
/-- The English object root *bone*. -/
def bone : Morph := .root "bone"
/-- The English object root *boy*. -/
def boy : Morph := .root "boy"
/-- The English pronoun *I*. -/
def i : Morph := .procl "I"
/-- The English action root *love*. -/
def love : Morph := .root "love"

/-- The English genitives *Kim's umbrella*, *the dog's bone* and *the boy I love's umbrella*. -/
def genitives : Inventory Morph where
  forms := [[kim, s_gen, umbrella], [the, dog, s_gen, bone], [the, boy, i, love, s_gen, umbrella]]
  rootClass m :=
    if m = love then some .action
    else if m = kim ∨ m = umbrella ∨ m = dog ∨ m = bone ∨ m = boy then some .object else none

/-- The German genitive *-s*. -/
def s_genDe : Morph := .suff "s"
/-- The German object root *Ring* 'ring'. -/
def ring : Morph := .root "Ring"

/-- The German genitive *Kim-s Ring* 'Kim's ring'. -/
def genitivesDe : Inventory Morph where
  forms := [[kim, s_genDe, ring]]
  rootClass m :=
    if m = kim ∨ m = ring then some .object else none

theorem genitive_clitic_suffix :
    genitives.IsClitic genitives.IsContentful s_gen ∧
      genitivesDe.IsAffix genitivesDe.IsContentful s_genDe := by
  decide

/-! ### Required affixes -/

/-- The Italian object root *alber* 'tree'. -/
def alber : Morph := .root "alber"
/-- The Italian singular suffix *-o*. -/
def o : Morph := .suff "o"
/-- The Italian plural suffix *-i*. -/
def i_pl : Morph := .suff "i"

/-- The Italian free forms *alber-o* 'tree' and *alber-i* 'trees'. -/
def italian : Inventory Morph where
  forms := [[alber, o], [alber, i_pl]]
  rootClass m := if m = alber then some .object else none

theorem alber_required :
    italian.IsRequiredAffix italian.IsContentful o alber ∧
      ¬ italian.IsWord italian.IsContentful [alber] ∧
      italian.IsWord italian.IsContentful [alber, o] := by
  decide

/-- The German action root *geb* 'give'. -/
def geb : Morph := .root "geb"
/-- The German imperative plural suffix *-t*. -/
def t : Morph := .suff "t"

/-- The German free forms *geb-en* '(to) give' and *geb-t* 'give (pl.)'. -/
def german : Inventory Morph where
  forms := [[geb, en], [geb, t]]
  rootClass m := if m = geb then some .action else none

theorem geb_required :
    german.IsRequiredAffix german.IsContentful en geb ∧
      ¬ german.IsWord german.IsContentful [geb] := by
  decide

/-- The English object root *tree*. -/
def tree : Morph := .root "tree"
/-- The English plural suffix *-s*. -/
def s_pl : Morph := .suff "s"
/-- The English object root *house*. -/
def house : Morph := .root "house"
/-- The English property root *big*. -/
def big : Morph := .root "big"

/-- The English free forms *a tree* and *trees*, with *a house* and *a big house* for the
article. -/
def trees : Inventory Morph where
  forms := [[a, tree], [tree, s_pl], [a, house], [a, big, house]]
  rootClass m :=
    if m = tree ∨ m = house then some .object else if m = big then some .property else none

theorem tree_word :
    ¬ trees.IsRequiredAffix trees.IsContentful s_pl tree ∧
      trees.IsWord trees.IsContentful [tree] ∧ [tree] ∉ trees.forms := by
  decide

/-! ### Bloomfield's minimum free form (§3.1) -/

theorem bloomfield_too_narrow :
    (trees.IsWord trees.IsContentful [tree] ∧
        ¬ IsMinimalFreeForm trees.forms [tree]) ∧
      infinitives.IsWord infinitives.IsContentful [«to»] ∧
        ¬ IsMinimalFreeForm infinitives.forms [«to»] :=
  ⟨⟨by decide, fun h ↦ by simpa [trees] using h.1⟩, by decide,
    fun h ↦ by simpa [infinitives] using h.1⟩

theorem bloomfield_too_broad :
    IsMinimalFreeForm trees.forms [a, tree] ∧
      ¬ trees.IsWord trees.IsContentful [a, tree] :=
  ⟨isMinimalFreeForm_of_take (by decide) (by decide), by decide⟩

/-! ### Words at an attachment -/

theorem wordsAt_affix_words :
    (∀ f ∈ trees.forms, ∀ w ∈ Morph.wordsAt .affix f,
        trees.IsWord trees.IsContentful w) ∧
      (∀ f ∈ italian.forms, ∀ w ∈ Morph.wordsAt .affix f,
        italian.IsWord italian.IsContentful w) ∧
      Morph.wordsAt .clitic [a, tree] = [[a, tree]] ∧
      ¬ trees.IsWord trees.IsContentful [a, tree] := by
  decide

end Haspelmath2023
