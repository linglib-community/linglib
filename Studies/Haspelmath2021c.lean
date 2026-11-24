/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Languages.Romance.Italian.Pronouns
public import Linglib.Morphology.Word.Distributional

/-!
# Haspelmath (2021): Bound forms, welded forms, and affixes: Basic concepts for morphological comparison

Haspelmath defines a bound form as a form that cannot occur on its own, a root as a morph that
denotes a thing, an action or a property, and an affix as a bound morph that is not a root, that
must occur on a root, and that cannot occur on roots of different root classes. A bound form
occurs on a root when it is next to the root or next to an affix that occurs on the root. The
affixes are `Morphology.Distributional.affixes` with the class a form denotes as its root class, and
this file checks them against the paper's examples. The Latin person suffixes are affixes through
the tense suffixes they follow. The Turkish person index is not an affix, because it also follows
the question particle. Markers that stand on roots of two classes are not affixes: the Polish
person clitics, the English article, the Russian question particle and preposition, and the case,
gender and number markers that nouns share with adjectives or verbs. The Italian object person
forms are affixes, on either side of the verb.

## Implementation notes

* Each example is a list of the paper's free forms, each a list of forms with the attachment its
  spelling gives it and the class of what it denotes. The paper's segmentations are kept, so
  Polish *domu* and *zrobili* are single morphs.
* The shape variants of a form are one morph: Italian *-mmi* is *mi*, and English *an* is *a*.
* The Polish demonstrative *to* is listed as a free form, since a morph counts as bound
  otherwise. The words of *hort-us nov-us*, *byl-a interesn-a* and *casa-s nueva-s* are
  listed as free forms beside the phrases, since in each phrase the first marker also stands next
  to the adjective.

## TODO

* Welded forms, the bound forms with shape variants conditioned by their host or conditioning
  shape variants of it, need morphs with shape variants.
* Read the free forms from example rows in boundary notation.

## References

* [haspelmath-2021c]
-/

@[expose] public section

namespace Haspelmath2021c

open Morphology Morphology.Distributional

/-! ### Latin -/

/-- The Latin action root *lauda-* 'praise'. -/
def lauda : Form := ⟨.root "lauda", some .action⟩
/-- The Latin second singular suffix *-s*. -/
def s : Form := ⟨.suff "s", none⟩
/-- The Latin future suffix *-bi*. -/
def bi : Form := ⟨.suff "bi", none⟩
/-- The Latin perfect suffix *-v*. -/
def v : Form := ⟨.suff "v", none⟩
/-- The Latin second singular perfect suffix *-isti*. -/
def isti : Form := ⟨.suff "isti", none⟩

/-- (16): The Latin free forms *lauda-s*, *lauda-bi-s* and *lauda-v-isti*. -/
def latin : List (List Form) :=
  [[lauda, s], [lauda, bi, s], [lauda, v, isti]]

/-- The four suffixes of (16) are affixes, and the person suffixes pass the definition only if the
tense suffixes they follow are affixes. -/
theorem latin_affixes :
    (∀ m ∈ [bi, v, s, isti], m ∈ affixes latin Form.meaning) ∧
      (∀ A : Set Form, bi ∉ A → ¬ AffixStep latin Form.meaning A s) ∧
      ∀ A : Set Form, v ∉ A → ¬ AffixStep latin Form.meaning A isti :=
  ⟨by decide,
    fun _ hA h ↦ absurd (h.mono (B := {z | z ≠ bi}) fun _ hz e ↦ hA (e ▸ hz)) (by decide),
    fun _ hA h ↦ absurd (h.mono (B := {z | z ≠ v}) fun _ hz e ↦ hA (e ▸ hz)) (by decide)⟩

/-! ### Turkish -/

/-- The Turkish action root *gel* 'come'. -/
def gel : Form := ⟨.root "gel", some .action⟩
/-- The Turkish progressive suffix *-iyor*. -/
def iyor : Form := ⟨.suff "iyor", none⟩
/-- The Turkish second singular *-sun*, written as a suffix. -/
def sun : Form := ⟨.suff "sun", none⟩
/-- The Turkish question particle *mu*, written apart. -/
def mu : Form := ⟨.encl "mu", none⟩
/-- The Turkish object root *su* 'water'. -/
def su : Form := ⟨.root "su", some .object⟩

/-- (18): The Turkish free forms *gel-iyor-sun*, *gel-iyor mu-sun* and *su mu*. -/
def turkish : List (List Form) :=
  [[gel, iyor, sun], [gel, iyor, mu, sun], [su, mu]]

/-- In (18), *-iyor* is an affix, the question particle *mu* follows a verb and a noun and is not,
and *-sun*, which follows *mu* in (18b), is not an affix either. -/
theorem turkish_affixes :
    iyor ∈ affixes turkish Form.meaning ∧
      mu ∉ affixes turkish Form.meaning ∧
      sun ∉ affixes turkish Form.meaning := by
  decide

/-! ### Markers on roots of two classes -/

/-- The Polish preposition *w* 'in'. -/
def w : Form := ⟨.procl "w", none⟩
/-- The Polish object form *domu* 'house'. -/
def domu : Form := ⟨.root "domu", some .object⟩
/-- The Polish demonstrative *to* 'that'. -/
def «to» : Form := ⟨.free "to", none⟩
/-- The Polish action form *zrobili* 'did'. -/
def zrobili : Form := ⟨.root "zrobili", some .action⟩
/-- The Polish second plural *=ście*. -/
def scie : Form := ⟨.encl "ście", none⟩

/-- (15): The Polish free forms *W domu to zrobili=ście?* and *W domu=ście to zrobili?*, with the
demonstrative *to*. -/
def polish : List (List Form) :=
  [[w, domu, «to», zrobili, scie], [w, domu, scie, «to», zrobili], [«to»]]

/-- In (15), *=ście* occurs on a verb and on a noun, so it is not an affix. -/
theorem scie_notMem_affixes : scie ∉ affixes polish Form.meaning := by
  decide

/-- The English indefinite article *a*, with the shape variant *an*. -/
def a : Form := ⟨.procl "a", none⟩
/-- The English object root *house*. -/
def house : Form := ⟨.root "house", some .object⟩
/-- The English object root *apple*. -/
def apple : Form := ⟨.root "apple", some .object⟩
/-- The English property root *big*. -/
def big : Form := ⟨.root "big", some .property⟩
/-- The English property root *open*. -/
def «open» : Form := ⟨.root "open", some .property⟩

/-- The English free forms *a house*, *an apple*, *a big house* and *an open house*. -/
def english : List (List Form) :=
  [[a, house], [a, apple], [a, big, house], [a, «open», house]]

-- The English indefinite article occurs on nouns and on prenominal adjectives.
theorem a_notMem_affixes : a ∉ affixes english Form.meaning := by
  decide

/-- The Russian action form *znaeš'* 'you know'. -/
def znaesh : Form := ⟨.root "znaeš'", some .action⟩
/-- The Russian property form *zdorov* 'well'. -/
def zdorov : Form := ⟨.root "zdorov", some .property⟩
/-- The Russian adverb *zdes'* 'here'. -/
def zdes : Form := ⟨.free "zdes'", none⟩
/-- The Russian interrogative enclitic *li*. -/
def li : Form := ⟨.encl "li", none⟩

/-- The Russian free forms *znaeš' li?*, *zdorov li?* and *zdes' li?*. -/
def russian : List (List Form) :=
  [[znaesh, li], [zdorov, li], [zdes, li]]

-- Russian *li* occurs on verbs, adjectives and adverbs.
theorem li_notMem_affixes : li ∉ affixes russian Form.meaning := by
  decide

/-- The Russian preposition *v* 'in'. -/
def v_in : Form := ⟨.procl "v", none⟩
/-- The Russian object root *Moskv-* 'Moscow'. -/
def moskv : Form := ⟨.root "Moskv", some .object⟩
/-- The Russian locative suffix *-e*. -/
def e_loc : Form := ⟨.suff "e", none⟩
/-- The Russian property form *bol'šom* 'big'. -/
def bolsom : Form := ⟨.root "bol'šom", some .property⟩
/-- The Russian object form *dome* 'house'. -/
def dome : Form := ⟨.root "dome", some .object⟩

/-- The Russian free forms *v Moskv-e* and *v bol'šom dome*. -/
def prepositions : List (List Form) :=
  [[v_in, moskv, e_loc], [v_in, bolsom, dome]]

-- The Russian preposition *v* occurs on noun roots and on adjective roots, so it is not a prefix.
theorem v_notMem_affixes : v_in ∉ affixes prepositions Form.meaning := by
  decide

/-- The Latin object root *hort-* 'garden'. -/
def hort : Form := ⟨.root "hort", some .object⟩
/-- The Latin property root *nov-* 'new'. -/
def nov : Form := ⟨.root "nov", some .property⟩
/-- The Latin nominative singular *-us*. -/
def us : Form := ⟨.suff "us", none⟩

/-- The Latin phrase *hort-us nov-us* and its words. -/
def latinCase : List (List Form) :=
  [[hort, us, nov, us], [hort, us], [nov, us]]

/-- The Russian action form *byl* 'was'. -/
def byl : Form := ⟨.root "byl", some .action⟩
/-- The Russian property root *interesn-* 'interesting'. -/
def interesn : Form := ⟨.root "interesn", some .property⟩
/-- The Russian feminine singular *-a*. -/
def a_f : Form := ⟨.suff "a", none⟩

/-- The Russian phrase *byl-a interesn-a* and its words. -/
def russianGender : List (List Form) :=
  [[byl, a_f, interesn, a_f], [byl, a_f], [interesn, a_f]]

/-- The Spanish object root *casa* 'house'. -/
def casa : Form := ⟨.root "casa", some .object⟩
/-- The Spanish property form *nueva* 'new'. -/
def nueva : Form := ⟨.root "nueva", some .property⟩
/-- The Spanish plural *-s*. -/
def s_pl : Form := ⟨.suff "s", none⟩

/-- The Spanish phrase *casa-s nueva-s* and its words. -/
def spanishNumber : List (List Form) :=
  [[casa, s_pl, nueva, s_pl], [casa, s_pl], [nueva, s_pl]]

/-- The Latin case marker *-us*, on nouns and adjectives, the Russian gender marker *-a*, on verbs
and adjectives, and the Spanish plural *-s*, on nouns and adjectives, are not affixes. -/
theorem agreement_notMem_affixes :
    us ∉ affixes latinCase Form.meaning ∧
      a_f ∉ affixes russianGender Form.meaning ∧
      s_pl ∉ affixes spanishNumber Form.meaning := by
  decide

/-! ### Italian -/

/-- The Italian first singular dative *mi*, with the shape variant *-mmi* after an imperative. -/
def mi : Form := ⟨.procl Italian.Pronouns.mi.form, none⟩
/-- The Italian action root *da* 'give'. -/
def da : Form := ⟨.root "da", some .action⟩

/-- (19): The Italian free forms *mi da* and *da-mmi*. -/
def italian : List (List Form) :=
  [[mi, da], [da, mi]]

/-- In (19), the object person form is an affix, before the verb root and after it, though the
Italian language file records it as a clitic. -/
theorem mi_mem_affixes :
    Italian.Pronouns.mi.strength = some .clitic ∧ mi ∈ affixes italian Form.meaning := by
  decide

end Haspelmath2021c
