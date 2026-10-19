module

public import Linglib.Syntax.Category.Verb.Defs
public import Linglib.Fragments.Finnish.Morphotactics

/-!
# Finnish verbs

A Finnish verb has two stems, the infinitive stem of the dictionary form, as *tul-* of *tul-la*
'come', and the inflectional stem of the present, as *tule-* of *tule-n* 'I come'. Karlsson
sorts the verbs into six conjugations, each named after a member, by how the two stems are
related, and consonant gradation gives the infinitive stem the weak grade where the
inflectional stem has the strong one, as in *hypät-ä* 'jump' against *hyppää-n* 'I jump'.
Gradation weakens a stem but does not strengthen one, so an entry gives its inflectional stem
and the conjugation forms the infinitive stem from it, as Karlsson forms that of a *huomat-a*
verb with a linking -t that causes gradation as an ending of one consonant does (§4.1.4).

A verb taking an infinitival complement governs its infinitive and case, the A infinitive for
*uskaltaa* 'dare', as in *uskals-i avat-a ove-n* 'dared to open the door', and the MA
infinitive illative for *pystyä* 'be able', as in *pysty-i tappelema-an* 'was able to fight'.
The entries include Nadathur's Finnish implicatives, with the polarity of the complement they
entail, and the verbs of the complements of those examples.

## Main definitions

* `Finnish.Conjugation`: Karlsson's six conjugations.
* `Finnish.Conjugation.infinitiveStem`: the infinitive stem formed from an inflectional stem.
* `Finnish.Verb`: a Finnish verb, the root `Verb` with its conjugation, its inflectional stem
  and the infinitive its complement takes.
* `Finnish.Verb.infinitive`, `Finnish.Verb.infinitiveForms`: the infinitives of a verb, and
  their forms in a case.
* `Finnish.verbs`: the entries.

## Main results

* `Finnish.Conjugation.infinitiveStem_tulla` and its siblings: the infinitive stem of each
  conjugation, from the shape of the inflectional stem Karlsson gives it.
* `Finnish.infinitiveStem_contracted`: the infinitive stems of Karlsson's contracted verbs.
* `Finnish.infinitiveStem_lukitse`: a *tarvit-a* verb whose stem gradation would weaken.
* `Finnish.ofString?_form`: the citation form of each entry is the A infinitive of the
  infinitive stem formed from its inflectional stem.
* `Finnish.wellFormed_complement`: the endings of each entry's complement make a word.

## Implementation notes

The infinitive stem gradates by `consonantGradation`, which weakens every stop its context
admits and lacks the alternation of /p/ after /l r/ and the assimilations, Karlsson's types (8)
to (12), so the stems of verbs like *kelvat-a* 'be good enough' and *lämm-et-ä*, with *kelpaa-*
and *lämp-ene-* in the inflectional stem, are not formed correctly.

## References

* [karlsson-2017]
* [nadathur-2023-implicatives]
-/

@[expose] public section

namespace Finnish

open Phonology Subregular.LocalRewrite

/-- The conjugations, named after a member (§6.2). -/
inductive Conjugation where
  /-- The *anta-a* 'give' verbs, whose infinitive ending follows a short vowel, have one
  stem. -/
  | antaa
  /-- The *saa-da* 'get' verbs, whose infinitive ending follows a long vowel or a diphthong,
  have one stem. -/
  | saada
  /-- The *tul-la* 'come' and *nous-ta* 'rise' verbs add -e to the infinitive stem. -/
  | tulla
  /-- The *huomat-a* 'notice' verbs have -A for the final -t of the infinitive stem. -/
  | huomata
  /-- The *tarvit-a* 'need' verbs add -se to the infinitive stem. -/
  | tarvita
  /-- The *lämm-et-ä* 'get warm' verbs have -ne for the final -t of the infinitive stem. -/
  | lämmetä
  deriving DecidableEq, Repr

namespace Conjugation

/-- The infinitive stem of a verb of the conjugation whose inflectional stem is `w`. It is `w`
itself for *anta-a* and *saa-da* verbs and `w` without its -se for *tarvit-a* verbs, which do
not gradate (§6.2.5). For *tul-la* verbs it is `w` without its -e, for *huomat-a* verbs `w`
with the linking -t for its last vowel (§4.1.4) and for *lämm-et-ä* verbs `w` with -t for its
-ne, in the weak grade. -/
def infinitiveStem : Conjugation → List Segment → List Segment
  | .antaa, w | .saada, w => w
  | .tulla, w => derive consonantGradation w.dropLast
  | .huomata, w => derive consonantGradation (w.dropLast ++ [t])
  | .tarvita, w => w.dropLast.dropLast
  | .lämmetä, w => derive consonantGradation (w.dropLast.dropLast ++ [t])

variable (w : List Segment)

@[simp] theorem infinitiveStem_antaa : antaa.infinitiveStem w = w := rfl

@[simp] theorem infinitiveStem_saada : saada.infinitiveStem w = w := rfl

@[simp] theorem infinitiveStem_tulla :
    tulla.infinitiveStem (w ++ [e]) = derive consonantGradation w := by
  simp [infinitiveStem]

@[simp] theorem infinitiveStem_huomata (x : Segment) :
    huomata.infinitiveStem (w ++ [x]) = derive consonantGradation (w ++ [t]) := by
  simp [infinitiveStem]

@[simp] theorem infinitiveStem_tarvita : tarvita.infinitiveStem (w ++ [s, e]) = w := by
  simp [infinitiveStem, List.dropLast_append_cons]

@[simp] theorem infinitiveStem_lämmetä :
    lämmetä.infinitiveStem (w ++ [n, e]) = derive consonantGradation (w ++ [t]) := by
  simp [infinitiveStem, List.dropLast_append_cons]

end Conjugation

/-- The infinitive stems of Karlsson's contracted verbs with the alternations (1) to (3) and (5)
to (7), *sieppaa-* 'snatch', *konttaa-* 'crawl', *hakkaa-* 'hew', *hautaa-* 'bury', *rahtaa-*
'freight' and *makaa-* 'lie', are *siepat-*, *kontat-*, *hakat-*, *haudat-*, *rahdat-* and
*maat-* (§4.1.4). -/
theorem infinitiveStem_contracted :
    Conjugation.huomata.infinitiveStem [s, i, e, p, p, a, a] = [s, i, e, p, a, t] ∧
      Conjugation.huomata.infinitiveStem [k, o, n, t, t, a, a] = [k, o, n, t, a, t] ∧
      Conjugation.huomata.infinitiveStem [h, a, k, k, a, a] = [h, a, k, a, t] ∧
      Conjugation.huomata.infinitiveStem [h, a, u, t, a, a] = [h, a, u, d, a, t] ∧
      Conjugation.huomata.infinitiveStem [r, a, h, t, a, a] = [r, a, h, d, a, t] ∧
      Conjugation.huomata.infinitiveStem [m, a, k, a, a] = [m, a, a, t] := by
  decide +kernel

/-- The infinitive stem of the *tarvit-a* verb *lukitse-* 'lock' is *lukit-*, which gradation
would weaken to *luit-* (§6.2.5). -/
theorem infinitiveStem_lukitse :
    Conjugation.tarvita.infinitiveStem [l, u, k, i, t, s, e] = [l, u, k, i, t] ∧
      derive consonantGradation [l, u, k, i, t] = [l, u, i, t] := by
  decide +kernel

/-- A Finnish verb is the root entry, whose `form` is the A infinitive, together with its
conjugation, its inflectional stem and the infinitive and case its complement takes. -/
structure Verb extends _root_.Verb where
  /-- The conjugation. -/
  conjugation : Conjugation
  /-- The inflectional stem, in the strong grade, on which the present and the MA and MINEN
  infinitives are built. -/
  inflectionalStem : List Segment
  /-- The infinitive and case of the complement. -/
  complement : Option (Infinitive × Case) := none

namespace Verb

/-- The infinitive stem, on which the A and E infinitives are built, is formed from the
inflectional stem as the conjugation forms it. -/
def infinitiveStem (v : Verb) : List Segment := v.conjugation.infinitiveStem v.inflectionalStem

/-- The stem of the infinitive `i`, the infinitive stem for the A and E infinitives and the
inflectional stem for the MA and MINEN infinitives (§6.1). -/
def stem (v : Verb) : Infinitive → List Segment
  | .a | .e => v.infinitiveStem
  | .ma | .minen => v.inflectionalStem

/-- The infinitive `i` of the verb before a case ending. -/
def infinitive (v : Verb) (i : Infinitive) : List Segment := surface (i.base (v.stem i))

/-- The surface forms of the infinitive `i` of the verb in the case `c`. -/
def infinitiveForms (v : Verb) (i : Infinitive) (c : Case) : List (List Segment) :=
  Nominal.realize (v.stem i) (i.endings c)

/-- The nominative of an infinitive is its form before a case ending. -/
@[simp] theorem infinitiveForms_nom (v : Verb) (i : Infinitive) :
    v.infinitiveForms i .nom = [v.infinitive i] := by
  simp [infinitiveForms, infinitive, Infinitive.endings, Nominal.realize, Nominal.continuations]

end Verb

/-! ### Entries -/

/-- *avata* 'open', with *avaa* 'opens' and the impersonal *avataan*. -/
def avata : Verb where
  morphs := [.root "avata"]
  valency := .ofFrame ArgumentFrame.np
  conjugation := .huomata
  inflectionalStem := [a, v, a, a]

/-- *korjata* 'repair, correct'. -/
def korjata : Verb where
  morphs := [.root "korjata"]
  valency := .ofFrame ArgumentFrame.np
  conjugation := .huomata
  inflectionalStem := [k, o, r, j, a, a]

/-- *vastata* 'answer'. -/
def vastata : Verb where
  morphs := [.root "vastata"]
  conjugation := .huomata
  inflectionalStem := [v, a, s, t, a, a]

/-- *haluta* 'want', with the A infinitive. -/
def haluta : Verb where
  morphs := [.root "haluta"]
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.infinitival, [0, 1])]
    (controllers := [none, some 0])
  conjugation := .huomata
  inflectionalStem := [h, a, l, u, a]
  complement := some (.a, .nom)

/-- *lukea* 'read'. -/
def lukea : Verb where
  morphs := [.root "lukea"]
  valency := .ofFrame ArgumentFrame.np
  conjugation := .antaa
  inflectionalStem := [l, u, k, e]

/-- *odottaa* 'wait'. -/
def odottaa : Verb where
  morphs := [.root "odottaa"]
  valency := .ofFrame ArgumentFrame.np
  conjugation := .antaa
  inflectionalStem := [o, d, o, t, t, a]

/-- *ottaa* 'take'. -/
def ottaa : Verb where
  morphs := [.root "ottaa"]
  valency := .ofFrame ArgumentFrame.np
  conjugation := .antaa
  inflectionalStem := [o, t, t, a]

/-- *tappaa* 'kill'. -/
def tappaa : Verb where
  morphs := [.root "tappaa"]
  valency := .ofFrame ArgumentFrame.np
  conjugation := .antaa
  inflectionalStem := [t, a, p, p, a]

/-- *kulkea* 'go, walk'. -/
def kulkea : Verb where
  morphs := [.root "kulkea"]
  valency := .ofFrame ArgumentFrame.intransitive
  conjugation := .antaa
  inflectionalStem := [k, u, l, k, e]

/-- *tulla* 'come'. -/
def tulla : Verb where
  morphs := [.root "tulla"]
  valency := .ofFrame ArgumentFrame.intransitive
  conjugation := .tulla
  inflectionalStem := [t, u, l, e]

/-- *nousta* 'rise'. -/
def nousta : Verb where
  morphs := [.root "nousta"]
  valency := .ofFrame ArgumentFrame.intransitive
  conjugation := .tulla
  inflectionalStem := [n, o, u, s, e]

/-- *tapella* 'fight', *tappele-* in the inflectional stem. -/
def tapella : Verb where
  morphs := [.root "tapella"]
  valency := .ofFrame ArgumentFrame.intransitive
  conjugation := .tulla
  inflectionalStem := [t, a, p, p, e, l, e]

/-- *paeta* 'flee', *pakene-* in the inflectional stem. -/
def paeta : Verb where
  morphs := [.root "paeta"]
  valency := .ofFrame ArgumentFrame.intransitive
  conjugation := .lämmetä
  inflectionalStem := [p, a, k, e, n, e]

/-! ### Implicative verbs

The positive implicatives entail their complement or its negation, *onnistua* 'manage' both
ways and *jaksaa* 'have the strength' only when negated. *Laiminlyödä* 'neglect' and
*epäröidä* 'hesitate' reverse the polarity. The subject controls the complement. -/

/-- *onnistua* 'succeed, manage', with the MA infinitive illative. -/
def onnistua : Verb where
  morphs := [.root "onnistua"]
  valency := .ofFrame ArgumentFrame.infinitival (controller := some 0)
  conjugation := .antaa
  inflectionalStem := [o, n, n, i, s, t, u]
  complement := some (.ma, .ill)
  implicative := ⟨.some .positive, .some .negative⟩

/-- *uskaltaa* 'dare'. -/
def uskaltaa : Verb where
  morphs := [.root "uskaltaa"]
  valency := .ofFrame ArgumentFrame.infinitival (controller := some 0)
  conjugation := .antaa
  inflectionalStem := [u, s, k, a, l, t, a]
  complement := some (.a, .nom)
  implicative := ⟨.some .positive, .some .negative⟩

/-- *viitsiä* 'bother'. -/
def viitsiä : Verb where
  morphs := [.root "viitsiä"]
  valency := .ofFrame ArgumentFrame.infinitival (controller := some 0)
  conjugation := .antaa
  inflectionalStem := [v, i, i, t, s, i]
  complement := some (.a, .nom)
  implicative := ⟨.some .positive, .some .negative⟩

/-- *malttaa* 'have the patience'. -/
def malttaa : Verb where
  morphs := [.root "malttaa"]
  valency := .ofFrame ArgumentFrame.infinitival (controller := some 0)
  conjugation := .antaa
  inflectionalStem := [m, a, l, t, t, a]
  complement := some (.a, .nom)
  implicative := ⟨.some .positive, .some .negative⟩

/-- *hennoa* 'have the heart'. -/
def hennoa : Verb where
  morphs := [.root "hennoa"]
  valency := .ofFrame ArgumentFrame.infinitival (controller := some 0)
  conjugation := .antaa
  inflectionalStem := [h, e, n, n, o]
  complement := some (.a, .nom)
  implicative := ⟨.some .positive, .some .negative⟩

/-- *kehdata* 'be unembarrassed, act without shame'. -/
def kehdata : Verb where
  morphs := [.root "kehdata"]
  valency := .ofFrame ArgumentFrame.infinitival (controller := some 0)
  conjugation := .huomata
  inflectionalStem := [k, e, h, t, a, a]
  complement := some (.a, .nom)
  implicative := ⟨.some .positive, .some .negative⟩

/-- *ehtiä* 'find time, make time'. -/
def ehtiä : Verb where
  morphs := [.root "ehtiä"]
  valency := .ofFrame ArgumentFrame.infinitival (controller := some 0)
  conjugation := .antaa
  inflectionalStem := [e, h, t, i]
  complement := some (.a, .nom)
  implicative := ⟨.some .positive, .some .negative⟩

/-- *jaksaa* 'have the strength'. -/
def jaksaa : Verb where
  morphs := [.root "jaksaa"]
  valency := .ofFrame ArgumentFrame.infinitival (controller := some 0)
  conjugation := .antaa
  inflectionalStem := [j, a, k, s, a]
  complement := some (.a, .nom)
  implicative := ⟨⊥, .some .negative⟩

/-- *mahtua* 'fit, be small enough', with the MA infinitive illative. -/
def mahtua : Verb where
  morphs := [.root "mahtua"]
  valency := .ofFrame ArgumentFrame.infinitival (controller := some 0)
  conjugation := .antaa
  inflectionalStem := [m, a, h, t, u]
  complement := some (.ma, .ill)
  implicative := ⟨⊥, .some .negative⟩

/-- *pystyä* 'be able', with the MA infinitive illative. -/
def pystyä : Verb where
  morphs := [.root "pystyä"]
  valency := .ofFrame ArgumentFrame.infinitival (controller := some 0)
  conjugation := .antaa
  inflectionalStem := [p, y, s, t, y]
  complement := some (.ma, .ill)
  implicative := ⟨⊥, .some .negative⟩

/-- *laiminlyödä* 'neglect'. -/
def laiminlyödä : Verb where
  morphs := [.root "laiminlyödä"]
  valency := .ofFrame ArgumentFrame.infinitival (controller := some 0)
  conjugation := .saada
  inflectionalStem := [l, a, i, m, i, n, l, y, ö]
  complement := some (.a, .nom)
  implicative := ⟨.some .negative, .some .positive⟩

/-- *epäröidä* 'hesitate'. -/
def epäröidä : Verb where
  morphs := [.root "epäröidä"]
  valency := .ofFrame ArgumentFrame.infinitival (controller := some 0)
  conjugation := .saada
  inflectionalStem := [e, p, ä, r, ö, i]
  complement := some (.a, .nom)
  implicative := ⟨⊥, .some .positive⟩

/-- The entries. -/
def verbs : List Verb :=
  [avata, korjata, vastata, haluta, lukea, odottaa, ottaa, tappaa, kulkea, tulla, nousta, tapella,
    paeta, onnistua, uskaltaa, viitsiä, malttaa, hennoa, kehdata, ehtiä, jaksaa, mahtua, pystyä,
    laiminlyödä, epäröidä]

/-- The citation form of each entry is the A infinitive of the infinitive stem formed from its
inflectional stem. -/
theorem ofString?_form : ∀ v ∈ verbs, ofString? v.form = some (v.infinitive .a) := by
  decide +kernel

/-- The endings of each entry's complement make a word. -/
theorem wellFormed_complement : ∀ v ∈ verbs, ∀ ic ∈ v.complement,
    Nominal.WellFormed (ic.1.endings ic.2) := by
  decide +kernel

end Finnish
