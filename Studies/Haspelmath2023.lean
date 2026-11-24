/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Root.Basic
public import Linglib.Morphology.Word.Distributional

/-!
# Haspelmath (2023): Defining the word

Haspelmath defines a word as a free morph, a clitic, or a root or compound possibly augmented
by nonrequired affixes and augmented by required affixes if there are any. A clitic is a bound
morph that is neither a root nor an affix, and a required affix is one that must be present in
a free form unless another affix replaces it. This file checks the definitions,
`Morphology.Distributional.IsWord` and its parts, against the paper's examples, and compares
the definition with Bloomfield's minimum free form, which it is meant to correct.

## Implementation notes

Each example is a list of the paper's free forms, each a list of forms with textbook attachment
labels and the class of what it denotes. The definition of an affix refers to the roots of
Definition 6, which needs a free form with the root as its only contentful morph; on the free
forms the paper cites for Definition 2 these are exactly the contentful morphs
(`roots_contentful`), and the other examples take the contentful morphs as roots. The English
article's distribution comes from the 2021 paper's *a house*, *a big house*. The genitive *'s* is
also given without a possessum, *the boy I love's*, since a noun follows it in each of the
paper's three forms. Compounds are not formalized.

## References

* [bloomfield-1933]
* [haspelmath-2021c]
* [haspelmath-2023]
-/

@[expose] public section

namespace Haspelmath2023

open Morphology Morphology.Distributional

/-! ### Roots -/

/-- The English possessive *my*. -/
def my : Form := ⟨.procl "my", none⟩
/-- The English object root *husband*. -/
def husband : Form := ⟨.root "husband", some .object⟩
/-- The English article *a*. -/
def a : Form := ⟨.procl "a", none⟩
/-- The English object root *café*. -/
def cafe : Form := ⟨.root "café", some .object⟩
/-- The English pronoun *he*. -/
def he : Form := ⟨.procl "he", none⟩
/-- The English auxiliary *is*. -/
def is : Form := ⟨.free "is", none⟩
/-- The English action root *work*. -/
def work : Form := ⟨.root "work", some .action⟩
/-- The English progressive suffix *-ing*. -/
def ing : Form := ⟨.suff "ing", none⟩
/-- The English property root *nice*. -/
def nice : Form := ⟨.root "nice", some .property⟩
/-- The English adverb *now*. -/
def now : Form := ⟨.free "now", none⟩
/-- The English interjection *ouch*. -/
def ouch : Form := ⟨.free "ouch", none⟩

/-- The English free forms cited for Definitions 1 and 2 are *nice*, *work*, *now*, *ouch*,
*my husband*, *a café* and *he is working*. -/
def freeForms : List (List Form) :=
  [[nice], [work], [now], [ouch], [my, husband], [a, cafe], [he, is, work, ing]]

-- Definition 6
theorem roots_contentful :
    ∀ m ∈ freeForms.flatten,
      IsRoot freeForms Form.meaning m ↔ m.meaning ≠ none := by
  decide

/-! ### Clitics and affixes -/

/-- The English infinitival *to*. -/
def «to» : Form := ⟨.procl "to", none⟩
/-- The English action root *destroy*. -/
def destroy : Form := ⟨.root "destroy", some .action⟩
/-- The English property root *thorough*. -/
def thorough : Form := ⟨.root "thorough", some .property⟩
/-- The English adverbial suffix *-ly*. -/
def ly : Form := ⟨.suff "ly", none⟩

/-- The English infinitives *to destroy* and *to thoroughly destroy*. -/
def infinitives : List (List Form) :=
  [[«to», destroy], [«to», thorough, ly, destroy]]

/-- The German particle *aus* 'out'. -/
def aus : Form := ⟨.pref "aus", none⟩
/-- The German infinitival *zu-*. -/
def zu : Form := ⟨.pref "zu", none⟩
/-- The German action root *geh* 'go'. -/
def geh : Form := ⟨.root "geh", some .action⟩
/-- The German infinitive suffix *-en*. -/
def en : Form := ⟨.suff "en", none⟩

/-- The German infinitive *aus-zu-gehen* 'to go out'. -/
def ausZuGehen : List (List Form) :=
  [[aus, zu, geh, en]]

/-- English *to* precedes an adverb as well as a verb, so it is a clitic, while German *zu-*
always occurs on a verb root and is a prefix. -/
theorem to_clitic_zu_prefix :
    IsClitic infinitives Form.meaning «to» ∧
      zu ∈ affixes ausZuGehen Form.meaning := by
  decide

/-- The English and German object root *Kim*. -/
def kim : Form := ⟨.root "Kim", some .object⟩
/-- The English genitive *'s*. -/
def s_gen : Form := ⟨.encl "s", none⟩
/-- The English object root *umbrella*. -/
def umbrella : Form := ⟨.root "umbrella", some .object⟩
/-- The English article *the*. -/
def the : Form := ⟨.procl "the", none⟩
/-- The English object root *dog*. -/
def dog : Form := ⟨.root "dog", some .object⟩
/-- The English object root *bone*. -/
def bone : Form := ⟨.root "bone", some .object⟩
/-- The English object root *boy*. -/
def boy : Form := ⟨.root "boy", some .object⟩
/-- The English pronoun *I*. -/
def i : Form := ⟨.procl "I", none⟩
/-- The English action root *love*. -/
def love : Form := ⟨.root "love", some .action⟩

/-- The English genitives *Kim's umbrella*, *the dog's bone* and *the boy I love's umbrella*, with
the last also without its possessum. -/
def genitives : List (List Form) :=
  [[kim, s_gen, umbrella], [the, dog, s_gen, bone], [the, boy, i, love, s_gen, umbrella],
     [the, boy, i, love, s_gen]]

/-- The German genitive *-s*. -/
def s_genDe : Form := ⟨.suff "s", none⟩
/-- The German object root *Ring* 'ring'. -/
def ring : Form := ⟨.root "Ring", some .object⟩

/-- The German genitive *Kim-s Ring* 'Kim's ring'. -/
def genitivesDe : List (List Form) :=
  [[kim, s_genDe, ring]]

/-- English *'s* also follows a verb, so it is a clitic, while German *-s* always follows a noun
and is a suffix. -/
theorem genitive_clitic_suffix :
    IsClitic genitives Form.meaning s_gen ∧
      s_genDe ∈ affixes genitivesDe Form.meaning := by
  decide

/-! ### Required affixes -/

/-- The Italian object root *alber* 'tree'. -/
def alber : Form := ⟨.root "alber", some .object⟩
/-- The Italian singular suffix *-o*. -/
def o : Form := ⟨.suff "o", none⟩
/-- The Italian plural suffix *-i*. -/
def i_pl : Form := ⟨.suff "i", none⟩

/-- The Italian free forms *alber-o* 'tree' and *alber-i* 'trees'. -/
def italian : List (List Form) :=
  [[alber, o], [alber, i_pl]]

/-- *alber* needs *-o* unless *-i* replaces it, so *-o* is a required affix, *alber* is not a
word and *alber-o* is. -/
theorem alber_required :
    IsRequiredAffix italian Form.meaning o alber ∧
      ¬ IsWord italian Form.meaning [alber] ∧
      IsWord italian Form.meaning [alber, o] := by
  decide

/-- The German action root *geb* 'give'. -/
def geb : Form := ⟨.root "geb", some .action⟩
/-- The German imperative plural suffix *-t*. -/
def t : Form := ⟨.suff "t", none⟩

/-- The German free forms *geb-en* '(to) give' and *geb-t* 'give (pl.)'. -/
def german : List (List Form) :=
  [[geb, en], [geb, t]]

/-- *geb* takes *-en* or the alternative required suffix *-t*, so the bare root is not a
word. -/
theorem geb_required :
    IsRequiredAffix german Form.meaning en geb ∧
      ¬ IsWord german Form.meaning [geb] := by
  decide

/-- The English object root *tree*. -/
def tree : Form := ⟨.root "tree", some .object⟩
/-- The English plural suffix *-s*. -/
def s_pl : Form := ⟨.suff "s", none⟩
/-- The English object root *house*. -/
def house : Form := ⟨.root "house", some .object⟩
/-- The English property root *big*. -/
def big : Form := ⟨.root "big", some .property⟩

/-- The English free forms *a tree* and *trees*, with *a house* and *a big house* for the
article. -/
def trees : List (List Form) :=
  [[a, tree], [tree, s_pl], [a, house], [a, big, house]]

/-- *-s* can be absent from a free form, as in *a tree*, without another affix replacing it, so
it is not required, and *tree* is a word although it is not a free form. -/
theorem tree_word :
    ¬ IsRequiredAffix trees Form.meaning s_pl tree ∧
      IsWord trees Form.meaning [tree] ∧ [tree] ∉ trees := by
  decide

/-! ### Bloomfield's minimum free form (§3.1) -/

/-- Bloomfield's definition is too narrow: *tree* and the clitic *to* are words but not free
forms, so not minimum free forms. -/
theorem bloomfield_too_narrow :
    (IsWord trees Form.meaning [tree] ∧
        ¬ IsMinimalFreeForm trees [tree]) ∧
      IsWord infinitives Form.meaning [«to»] ∧
        ¬ IsMinimalFreeForm infinitives [«to»] :=
  ⟨⟨by decide, fun h ↦ by simpa [trees] using h.1⟩, by decide,
    fun h ↦ by simpa [infinitives] using h.1⟩

/-- Bloomfield's definition is too broad: *a tree* cannot be broken up into free forms, so it
is a minimum free form, but it is a clitic and a root, not a word. -/
theorem bloomfield_too_broad :
    IsMinimalFreeForm trees [a, tree] ∧
      ¬ IsWord trees Form.meaning [a, tree] :=
  ⟨isMinimalFreeForm_of_take (by decide) (by decide), by decide⟩

/-! ### Words at an attachment -/

/-- The words of a sequence of forms at an attachment are the maximal runs whose morphs join at
it. -/
def wordsAt (l : Morph.Attachment) (fs : List Form) : List (List Form) :=
  fs.splitBy fun x y ↦ decide (Morph.JoinsAt l x.shape y.shape)

/-- The words at `.affix` of the English forms with *tree* and of the Italian forms are words,
while *a=tree*, one word at `.clitic`, is not. -/
theorem wordsAt_affix_words :
    (∀ f ∈ trees, ∀ w ∈ wordsAt .affix f, IsWord trees Form.meaning w) ∧
      (∀ f ∈ italian, ∀ w ∈ wordsAt .affix f, IsWord italian Form.meaning w) ∧
      wordsAt .clitic [a, tree] = [[a, tree]] ∧
      ¬ IsWord trees Form.meaning [a, tree] := by
  decide

end Haspelmath2023
