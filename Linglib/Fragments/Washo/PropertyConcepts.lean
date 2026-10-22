module

public import Linglib.Semantics.Root.PropertyConcept
public import Linglib.Syntax.Category.Verb.Defs

/-!
# Washo property concepts

Washo has no adjectives: its property concepts are intransitive verbs of three morphological
classes. A Class 1 verb is the bare root, a Class 2 verb is the root with the suffix *-iʔ*, and a
Class 3 verb is a reduplicated root flanked by the prefix *ʔil-* and *-iʔ*. The entries are the
seventy stems of Hanink and Koontz-Garboden's appendix, with their Dixon categories; most stems
are from the Washo Archive, and the reduplicated stems are cited reduplicated. Orthography
follows Jacobsen: *:* marks length, *ʔ* the glottal stop, *ɨ* the high central vowel, *’*
glottalization, and capital *L* and *M* voiceless sonorants.

## Main declarations

* `Washo.iq`, `Washo.il`: the suffix *-iʔ* and the prefix *ʔil-*.
* `Washo.PropertyConcept`: a property-concept verb with its Dixon category.
* `Washo.PropertyConcept.shape`: the class of a verb, read off its affixes.
* `Washo.propertyConcepts`: the seventy stems of the appendix.

## References

* [hanink-koontz-garboden-2025]
* [dixon-1982]
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

/-- A property-concept verb is a verb entry whose morphs are its root and the affixes of its
class, with the Dixon category of its root. -/
structure PropertyConcept extends _root_.Verb where
  /-- The Dixon category of the root, as the appendix assigns it. -/
  category : Semantics.PropertyConcept.Class

namespace PropertyConcept

variable (root : String) (c : Semantics.PropertyConcept.Class)

/-- The Class 1 verb of a root, inflected like any intransitive verb. -/
def bare : PropertyConcept where
  morphs := [.root root]
  valency := .ofFrame .intransitive
  category := c

/-- The Class 2 verb of a root. -/
def suffixed : PropertyConcept where
  morphs := [.root root, iq]
  valency := .ofFrame .intransitive
  category := c

/-- The Class 3 verb of a reduplicated root. -/
def prefixed : PropertyConcept where
  morphs := [il, .root root, iq]
  valency := .ofFrame .intransitive
  category := c

/-- The class of a verb is read off its affixes: *ʔil-* marks Class 3, and *-iʔ* without it
Class 2. -/
def shape (e : PropertyConcept) : Shape :=
  if il ∈ e.morphs then .prefixed else if iq ∈ e.morphs then .suffixed else .bare

end PropertyConcept

/-! ### Age -/

/-- *MiLe* 'old'. -/
def MiLe : PropertyConcept := .bare "MiLe" .age

/-- *ešlut’* 'young'. -/
def ešlut : PropertyConcept := .suffixed "ešlut’" .age

/-! ### Color -/

/-- *leleg* 'red'. -/
def leleg : PropertyConcept := .prefixed "leleg" .color

/-- *p’ilp’il* 'blue'. -/
def pilpil : PropertyConcept := .prefixed "p’ilp’il" .color

/-- *popo* 'white'. -/
def popo : PropertyConcept := .prefixed "popo" .color

/-- *šošoŋ* 'brown'. -/
def šošoŋ : PropertyConcept := .prefixed "šošoŋ" .color

/-- *ʔyɨŋʔyɨŋ* 'varicolored'. -/
def yiŋyiŋ : PropertyConcept := .prefixed "ʔyɨŋʔyɨŋ" .color

/-! ### Dimension -/

/-- *beheziŋ* 'small'. -/
def beheziŋ : PropertyConcept := .bare "beheziŋ" .dimension

/-- *wgohat* 'wide', from [bochnak-2013]. -/
def wgohat : PropertyConcept := .bare "wgohat" .dimension

/-- *ʔlupdep* 'thin (of object)'. -/
def lupdep : PropertyConcept := .bare "ʔlupdep" .dimension

/-- *ʔudaw* 'tall (of object)'. -/
def udaw : PropertyConcept := .bare "ʔudaw" .dimension

/-- *i:yel* 'big'. -/
def iyel : PropertyConcept := .suffixed "i:yel" .dimension

/-- *hamham* 'light (in weight)'. -/
def hamham : PropertyConcept := .prefixed "hamham" .dimension

/-- *šɨšɨš* 'heavy'. -/
def šišiš : PropertyConcept := .prefixed "šɨšɨš" .dimension

/-! ### Human propensity -/

/-- *bišapuʔ* 'hungry'. -/
def bišapu : PropertyConcept := .bare "bišapuʔ" .humanPropensity

/-- *gumbiʔis* 'proud'. -/
def gumbiis : PropertyConcept := .bare "gumbiʔis" .humanPropensity

/-- *gumyoʔl* 'tired'. -/
def gumyol : PropertyConcept := .bare "gumyoʔl" .humanPropensity

/-- *k’iwɨl* 'sharp-thinking'. -/
def kiwil : PropertyConcept := .bare "k’iwɨl" .humanPropensity

/-- *Lokaš* 'afraid'. -/
def Lokaš : PropertyConcept := .bare "Lokaš" .humanPropensity

/-- *meleyɨk* 'inebriated', from [bochnak-etal-2011]. -/
def meleyik : PropertyConcept := .bare "meleyɨk" .humanPropensity

/-- *melot’ik* 'thirsty'. -/
def melotik : PropertyConcept := .bare "melot’ik" .humanPropensity

/-- *šašɨw* 'afraid'. -/
def šašiw : PropertyConcept := .bare "šašɨw" .humanPropensity

/-- *t’e:su* 'jealous'. -/
def tesu : PropertyConcept := .bare "t’e:su" .humanPropensity

/-- *yaha* 'sick/hurt'. -/
def yaha : PropertyConcept := .bare "yaha" .humanPropensity

/-- *yomuŋ* 'full (from eating)'. -/
def yomuŋ : PropertyConcept := .bare "yomuŋ" .humanPropensity

/-- *yumɨl* 'full (from eating)'. -/
def yumil : PropertyConcept := .bare "yumɨl" .humanPropensity

/-- *gumsut’ɨm* 'brave'. -/
def gumsutim : PropertyConcept := .suffixed "gumsut’ɨm" .humanPropensity

/-- *musiw* 'generous'. -/
def musiw : PropertyConcept := .suffixed "musiw" .humanPropensity

/-- *tamugayʔl* 'bored'. -/
def tamugayl : PropertyConcept := .suffixed "tamugayʔl" .humanPropensity

/-! ### Value -/

/-- *ʔaŋaw* 'good'. -/
def aŋaw : PropertyConcept := .bare "ʔaŋaw" .value

/-- *mu:ʔaŋ* 'tasty'. -/
def muaŋ : PropertyConcept := .suffixed "mu:ʔaŋ" .value

/-- *ʔnu:š* 'poor condition'. -/
def nuš : PropertyConcept := .suffixed "ʔnu:š" .value

/-- *ʔumbiʔic’* 'expensive'. -/
def umbiic : PropertyConcept := .suffixed "ʔumbiʔic’" .value

/-! ### Physical property -/

/-- *golgoš* 'short and fat'. -/
def golgoš : PropertyConcept := .bare "golgoš" .physicalProperty

/-- *ibik’* 'ripe'. -/
def ibik : PropertyConcept := .bare "ibik’" .physicalProperty

/-- *ihuk’* 'dry'. -/
def ihuk : PropertyConcept := .bare "ihuk’" .physicalProperty

/-- *k’eše* 'alive'. -/
def keše : PropertyConcept := .bare "k’eše" .physicalProperty

/-- *metuʔ* 'cold'. -/
def metu : PropertyConcept := .bare "metuʔ" .physicalProperty

/-- *mi:p’ɨl* 'full'. -/
def mipil : PropertyConcept := .bare "mi:p’ɨl" .physicalProperty

/-- *mosot* 'wet'. -/
def mosot : PropertyConcept := .bare "mosot" .physicalProperty

/-- *muc’uc’u* 'sweet'. -/
def mucucu : PropertyConcept := .bare "muc’uc’u" .physicalProperty

/-- *wɨhl* 'cold'. -/
def wihl : PropertyConcept := .bare "wɨhl" .physicalProperty

/-- *yak’aš* 'warm'. -/
def yakaš : PropertyConcept := .bare "yak’aš" .physicalProperty

/-- *yasaŋ* 'hot'. -/
def yasaŋ : PropertyConcept := .bare "yasaŋ" .physicalProperty

/-- *ʔyaʔyaŋ* 'naked'. -/
def yayaŋ : PropertyConcept := .bare "ʔyaʔyaŋ" .physicalProperty

/-- *guc’u* 'torn'. -/
def gucu : PropertyConcept := .suffixed "guc’u" .physicalProperty

/-- *gumbeyéc’ɨk* 'closed'. -/
def gumbeyécik : PropertyConcept := .suffixed "gumbeyéc’ɨk" .physicalProperty

/-- *kakt* 'quiet'. -/
def kakt : PropertyConcept := .suffixed "kakt" .physicalProperty

/-- *Loyaw* 'dark'. -/
def Loyaw : PropertyConcept := .suffixed "Loyaw" .physicalProperty

/-- *nuʔuš* 'stinky'. -/
def nuuš : PropertyConcept := .suffixed "nuʔuš" .physicalProperty

/-- *wkuliʔ* 'solid', from the tribal dictionary. -/
def wkuli : PropertyConcept := .suffixed "wkuliʔ" .physicalProperty

/-- *yac’im* 'smoky'. -/
def yacim : PropertyConcept := .suffixed "yac’im" .physicalProperty

/-- *ba:bab* 'spotted'. -/
def babab : PropertyConcept := .prefixed "ba:bab" .physicalProperty

/-- *hu:hu* 'striped'. -/
def huhu : PropertyConcept := .prefixed "hu:hu" .physicalProperty

/-- *k’awk’aw* 'closed', from [jacobsen-1980]. -/
def kawkaw : PropertyConcept := .prefixed "k’awk’aw" .physicalProperty

/-- *k’unk’un* 'bent'. -/
def kunkun : PropertyConcept := .prefixed "k’unk’un" .physicalProperty

/-- *kaykay* 'tall'. -/
def kaykay : PropertyConcept := .prefixed "kaykay" .physicalProperty

/-- *kuškuš* 'short and fat'. -/
def kuškuš : PropertyConcept := .prefixed "kuškuš" .physicalProperty

/-- *lotlot* 'soft'. -/
def lotlot : PropertyConcept := .prefixed "lotlot" .physicalProperty

/-- *mukmuk* 'chubby'. -/
def mukmuk : PropertyConcept := .prefixed "mukmuk" .physicalProperty

/-- *naynay* 'muddy'. -/
def naynay : PropertyConcept := .prefixed "naynay" .physicalProperty

/-- *p’ep’el* 'bitter'. -/
def pepel : PropertyConcept := .prefixed "p’ep’el" .physicalProperty

/-- *p’ɨp’ɨ* 'thin', from the tribal dictionary. -/
def pipi : PropertyConcept := .prefixed "p’ɨp’ɨ" .physicalProperty

/-- *šapšap* 'fuzzy'. -/
def šapšap : PropertyConcept := .prefixed "šapšap" .physicalProperty

/-- *ši:šip* 'straight', from [jacobsen-1980]. -/
def šišip : PropertyConcept := .prefixed "ši:šip" .physicalProperty

/-- *sɨnsɨn* 'thin'. -/
def sinsin : PropertyConcept := .prefixed "sɨnsɨn" .physicalProperty

/-- *siwsiw* 'smooth', from [jacobsen-1980]. -/
def siwsiw : PropertyConcept := .prefixed "siwsiw" .physicalProperty

/-- *t’et’ep* 'fat'. -/
def tetep : PropertyConcept := .prefixed "t’et’ep" .physicalProperty

/-- *t’ɨnt’ɨn* 'rough'. -/
def tintin : PropertyConcept := .prefixed "t’ɨnt’ɨn" .physicalProperty

/-- *witwit* 'stiff'. -/
def witwit : PropertyConcept := .prefixed "witwit" .physicalProperty

/-- The seventy stems of the appendix. -/
def propertyConcepts : List PropertyConcept :=
  [MiLe, ešlut, leleg, pilpil, popo, šošoŋ, yiŋyiŋ, beheziŋ, wgohat, lupdep, udaw, iyel, hamham,
    šišiš, bišapu, gumbiis, gumyol, kiwil, Lokaš, meleyik, melotik, šašiw, tesu, yaha, yomuŋ,
    yumil, gumsutim, musiw, tamugayl, aŋaw, muaŋ, nuš, umbiic, golgoš, ibik, ihuk, keše, metu,
    mipil, mosot, mucucu, wihl, yakaš, yasaŋ, yayaŋ, gucu, gumbeyécik, kakt, Loyaw, nuuš, wkuli,
    yacim, babab, huhu, kawkaw, kunkun, kaykay, kuškuš, lotlot, mukmuk, naynay, pepel, pipi,
    šapšap, šišip, sinsin, siwsiw, tetep, tintin, witwit]

end Washo
