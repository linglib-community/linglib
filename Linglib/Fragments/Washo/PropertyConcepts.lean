module

public import Linglib.Syntax.Category.Verb.Defs

/-!
# Washo property concepts

Washo has no adjectives: its property concepts are intransitive verbs of three morphological
classes. A Class 1 verb is the bare root, a Class 2 verb is the root with the suffix *-iʔ*, and a
Class 3 verb is a reduplicated root flanked by the prefix *ʔil-* and *-iʔ*. The entries are the
seventy stems of Hanink and Koontz-Garboden's appendix, in its order; most stems are from the
Washo Archive, and the reduplicated stems are cited reduplicated. Orthography
follows Jacobsen: *:* marks length, *ʔ* the glottal stop, *ɨ* the high central vowel, *’*
glottalization, and capital *L* and *M* voiceless sonorants.

## Main declarations

* `Washo.iq`, `Washo.il`: the suffix *-iʔ* and the prefix *ʔil-*.
* `Washo.Shape.verb`: the property-concept verb of a class on a root.
* `Washo.shape`: the class of a verb, read off its affixes.
* `Washo.propertyConcepts`: the seventy stems of the appendix.

## References

* [hanink-koontz-garboden-2025]
* [jacobsen-1964]
* [jacobsen-1980]
* [bochnak-2013]
* [bochnak-etal-2011]
-/

@[expose] public section

namespace Washo

open Morphology (Morph)

/-- The suffix *-iʔ*, which [jacobsen-1964] calls attributive-agentive. -/
def iq : Morph := .suff "iʔ"

/-- The prefix *ʔil-*, glossed attributive, which reduplicates the root it attaches to
([jacobsen-1980]). -/
def il : Morph := .pref "ʔil"

/-- The class of a property-concept verb. -/
inductive Shape where
  /-- The bare root, with subject agreement and mood only: *ʔíhuk’i* 'it is dry'. -/
  | bare
  /-- The root with the suffix *-iʔ*: *ʔí:yeliʔi* 'it is big'. -/
  | suffixed
  /-- The reduplicated root with the prefix *ʔil-* and the suffix *-iʔ*: *ʔilkáykayiʔi* 'he is
  tall'. -/
  | prefixed
  deriving DecidableEq, Repr, Fintype

/-- The property-concept verb of a class on a root is an intransitive verb whose morphs are the
root and the affixes of the class; a Class 3 root is given reduplicated. -/
def Shape.verb (s : Shape) (root : String) : Verb where
  morphs := match s with
    | .bare => [.root root]
    | .suffixed => [.root root, iq]
    | .prefixed => [il, .root root, iq]
  valency := .ofFrame .intransitive

/-- The class of a verb is read off its affixes: *ʔil-* marks Class 3, and *-iʔ* without it
Class 2. -/
def shape (e : Verb) : Shape :=
  if il ∈ e.morphs then .prefixed else if iq ∈ e.morphs then .suffixed else .bare

@[simp] theorem shape_verb (s : Shape) (root : String) : shape (s.verb root) = s := by
  cases s <;> simp [shape, Shape.verb, il, iq, Morph.root, Morph.pref, Morph.suff]

/-- *MiLe* 'old'. -/
def MiLe : Verb := Shape.bare.verb "MiLe"

/-- *ešlut’* 'young'. -/
def ešlut : Verb := Shape.suffixed.verb "ešlut’"

/-- *leleg* 'red'. -/
def leleg : Verb := Shape.prefixed.verb "leleg"

/-- *p’ilp’il* 'blue'. -/
def pilpil : Verb := Shape.prefixed.verb "p’ilp’il"

/-- *popo* 'white'. -/
def popo : Verb := Shape.prefixed.verb "popo"

/-- *šošoŋ* 'brown'. -/
def šošoŋ : Verb := Shape.prefixed.verb "šošoŋ"

/-- *ʔyɨŋʔyɨŋ* 'varicolored'. -/
def yiŋyiŋ : Verb := Shape.prefixed.verb "ʔyɨŋʔyɨŋ"

/-- *beheziŋ* 'small'. -/
def beheziŋ : Verb := Shape.bare.verb "beheziŋ"

/-- *wgohat* 'wide', from [bochnak-2013]. -/
def wgohat : Verb := Shape.bare.verb "wgohat"

/-- *ʔlupdep* 'thin (of object)'. -/
def lupdep : Verb := Shape.bare.verb "ʔlupdep"

/-- *ʔudaw* 'tall (of object)'. -/
def udaw : Verb := Shape.bare.verb "ʔudaw"

/-- *i:yel* 'big'. -/
def iyel : Verb := Shape.suffixed.verb "i:yel"

/-- *hamham* 'light (in weight)'. -/
def hamham : Verb := Shape.prefixed.verb "hamham"

/-- *šɨšɨš* 'heavy'. -/
def šišiš : Verb := Shape.prefixed.verb "šɨšɨš"

/-- *bišapuʔ* 'hungry'. -/
def bišapu : Verb := Shape.bare.verb "bišapuʔ"

/-- *gumbiʔis* 'proud'. -/
def gumbiis : Verb := Shape.bare.verb "gumbiʔis"

/-- *gumyoʔl* 'tired'. -/
def gumyol : Verb := Shape.bare.verb "gumyoʔl"

/-- *k’iwɨl* 'sharp-thinking'. -/
def kiwil : Verb := Shape.bare.verb "k’iwɨl"

/-- *Lokaš* 'afraid'. -/
def Lokaš : Verb := Shape.bare.verb "Lokaš"

/-- *meleyɨk* 'inebriated', from [bochnak-etal-2011]. -/
def meleyik : Verb := Shape.bare.verb "meleyɨk"

/-- *melot’ik* 'thirsty'. -/
def melotik : Verb := Shape.bare.verb "melot’ik"

/-- *šašɨw* 'afraid'. -/
def šašiw : Verb := Shape.bare.verb "šašɨw"

/-- *t’e:su* 'jealous'. -/
def tesu : Verb := Shape.bare.verb "t’e:su"

/-- *yaha* 'sick/hurt'. -/
def yaha : Verb := Shape.bare.verb "yaha"

/-- *yomuŋ* 'full (from eating)'. -/
def yomuŋ : Verb := Shape.bare.verb "yomuŋ"

/-- *yumɨl* 'full (from eating)'. -/
def yumil : Verb := Shape.bare.verb "yumɨl"

/-- *gumsut’ɨm* 'brave'. -/
def gumsutim : Verb := Shape.suffixed.verb "gumsut’ɨm"

/-- *musiw* 'generous'. -/
def musiw : Verb := Shape.suffixed.verb "musiw"

/-- *tamugayʔl* 'bored'. -/
def tamugayl : Verb := Shape.suffixed.verb "tamugayʔl"

/-- *ʔaŋaw* 'good'. -/
def aŋaw : Verb := Shape.bare.verb "ʔaŋaw"

/-- *mu:ʔaŋ* 'tasty'. -/
def muaŋ : Verb := Shape.suffixed.verb "mu:ʔaŋ"

/-- *ʔnu:š* 'poor condition'. -/
def nuš : Verb := Shape.suffixed.verb "ʔnu:š"

/-- *ʔumbiʔic’* 'expensive'. -/
def umbiic : Verb := Shape.suffixed.verb "ʔumbiʔic’"

/-- *golgoš* 'short and fat'. -/
def golgoš : Verb := Shape.bare.verb "golgoš"

/-- *ibik’* 'ripe'. -/
def ibik : Verb := Shape.bare.verb "ibik’"

/-- *ihuk’* 'dry'. -/
def ihuk : Verb := Shape.bare.verb "ihuk’"

/-- *k’eše* 'alive'. -/
def keše : Verb := Shape.bare.verb "k’eše"

/-- *metuʔ* 'cold'. -/
def metu : Verb := Shape.bare.verb "metuʔ"

/-- *mi:p’ɨl* 'full'. -/
def mipil : Verb := Shape.bare.verb "mi:p’ɨl"

/-- *mosot* 'wet'. -/
def mosot : Verb := Shape.bare.verb "mosot"

/-- *muc’uc’u* 'sweet'. -/
def mucucu : Verb := Shape.bare.verb "muc’uc’u"

/-- *wɨhl* 'cold'. -/
def wihl : Verb := Shape.bare.verb "wɨhl"

/-- *yak’aš* 'warm'. -/
def yakaš : Verb := Shape.bare.verb "yak’aš"

/-- *yasaŋ* 'hot'. -/
def yasaŋ : Verb := Shape.bare.verb "yasaŋ"

/-- *ʔyaʔyaŋ* 'naked'. -/
def yayaŋ : Verb := Shape.bare.verb "ʔyaʔyaŋ"

/-- *guc’u* 'torn'. -/
def gucu : Verb := Shape.suffixed.verb "guc’u"

/-- *gumbeyéc’ɨk* 'closed'. -/
def gumbeyécik : Verb := Shape.suffixed.verb "gumbeyéc’ɨk"

/-- *kakt* 'quiet'. -/
def kakt : Verb := Shape.suffixed.verb "kakt"

/-- *Loyaw* 'dark'. -/
def Loyaw : Verb := Shape.suffixed.verb "Loyaw"

/-- *nuʔuš* 'stinky'. -/
def nuuš : Verb := Shape.suffixed.verb "nuʔuš"

/-- *wkuliʔ* 'solid', from the tribal dictionary. -/
def wkuli : Verb := Shape.suffixed.verb "wkuliʔ"

/-- *yac’im* 'smoky'. -/
def yacim : Verb := Shape.suffixed.verb "yac’im"

/-- *ba:bab* 'spotted'. -/
def babab : Verb := Shape.prefixed.verb "ba:bab"

/-- *hu:hu* 'striped'. -/
def huhu : Verb := Shape.prefixed.verb "hu:hu"

/-- *k’awk’aw* 'closed', from [jacobsen-1980]. -/
def kawkaw : Verb := Shape.prefixed.verb "k’awk’aw"

/-- *k’unk’un* 'bent'. -/
def kunkun : Verb := Shape.prefixed.verb "k’unk’un"

/-- *kaykay* 'tall'. -/
def kaykay : Verb := Shape.prefixed.verb "kaykay"

/-- *kuškuš* 'short and fat'. -/
def kuškuš : Verb := Shape.prefixed.verb "kuškuš"

/-- *lotlot* 'soft'. -/
def lotlot : Verb := Shape.prefixed.verb "lotlot"

/-- *mukmuk* 'chubby'. -/
def mukmuk : Verb := Shape.prefixed.verb "mukmuk"

/-- *naynay* 'muddy'. -/
def naynay : Verb := Shape.prefixed.verb "naynay"

/-- *p’ep’el* 'bitter'. -/
def pepel : Verb := Shape.prefixed.verb "p’ep’el"

/-- *p’ɨp’ɨ* 'thin', from the tribal dictionary. -/
def pipi : Verb := Shape.prefixed.verb "p’ɨp’ɨ"

/-- *šapšap* 'fuzzy'. -/
def šapšap : Verb := Shape.prefixed.verb "šapšap"

/-- *ši:šip* 'straight', from [jacobsen-1980]. -/
def šišip : Verb := Shape.prefixed.verb "ši:šip"

/-- *sɨnsɨn* 'thin'. -/
def sinsin : Verb := Shape.prefixed.verb "sɨnsɨn"

/-- *siwsiw* 'smooth', from [jacobsen-1980]. -/
def siwsiw : Verb := Shape.prefixed.verb "siwsiw"

/-- *t’et’ep* 'fat'. -/
def tetep : Verb := Shape.prefixed.verb "t’et’ep"

/-- *t’ɨnt’ɨn* 'rough'. -/
def tintin : Verb := Shape.prefixed.verb "t’ɨnt’ɨn"

/-- *witwit* 'stiff'. -/
def witwit : Verb := Shape.prefixed.verb "witwit"

/-- The seventy stems of the appendix. -/
def propertyConcepts : List Verb :=
  [MiLe, ešlut, leleg, pilpil, popo, šošoŋ, yiŋyiŋ, beheziŋ, wgohat, lupdep, udaw, iyel, hamham,
    šišiš, bišapu, gumbiis, gumyol, kiwil, Lokaš, meleyik, melotik, šašiw, tesu, yaha, yomuŋ,
    yumil, gumsutim, musiw, tamugayl, aŋaw, muaŋ, nuš, umbiic, golgoš, ibik, ihuk, keše, metu,
    mipil, mosot, mucucu, wihl, yakaš, yasaŋ, yayaŋ, gucu, gumbeyécik, kakt, Loyaw, nuuš, wkuli,
    yacim, babab, huhu, kawkaw, kunkun, kaykay, kuškuš, lotlot, mukmuk, naynay, pepel, pipi,
    šapšap, šišip, sinsin, siwsiw, tetep, tintin, witwit]

end Washo
