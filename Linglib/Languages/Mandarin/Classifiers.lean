module

public import Linglib.Syntax.Category.Classifier.Basic
public import Mathlib.Data.Finset.Insert

/-!
# Mandarin classifiers

A Mandarin noun is counted, and pointed out with a demonstrative, through a classifier: *sān ge
rén* 'three people', *zhèi zhǎn dēng* 'this lamp', *nèi liù běn shū* 'those six books'. The
quantifiers *zhěng* 'whole', *jǐ* 'how many, a few', *mǒu yī* 'a certain' and *měi* 'every' take
one too. The language has several dozen classifiers, and the noun chooses: each noun has its own
classifier, which is learned with it. There is some regularity in the meanings of the nouns a
classifier counts, as *tiáo* counts snakes, ropes, roads, rivers, tails and fish, but *tiáo*
also counts most four-legged mammals and the news and the law, while the elongated brush-pen
and arrow take *zhī* 枝. Some nouns take two classifiers according to their meaning: *shū*
'book' is counted with *běn* as a thing and with *bù* as a work. *Gè* is the general classifier,
applicable to every individual noun beside its own classifier, and many speakers now use it in
place of the specific ones. A noun that itself denotes a measure, such as *tiān* 'day', takes
no classifier.

Measure words stand in the same position: standard measures such as *bàng* 'pound', aggregates such
as *qún* 'flock', and containers such as *píng* 'bottle'. Container measures are nouns used as
measures, an open class, and unlike a classifier, which takes no *de* before its noun, a container
measure can always take *de*. The container measures below are examples.

## Main definitions

* `Mandarin.Classifiers.classifiers` — the individual classifiers entered here.
* `Mandarin.Classifiers.containerMeasures` — the container measures entered here.

Which nouns each classifier counts is recorded on the nouns (`Mandarin.Nouns`).

## References

* [li-thompson-1981]
* [chao-1968]
-/

@[expose] public section

namespace Mandarin.Classifiers

/-! ### Individual classifiers -/

/-- *gè* 个, the general classifier: *sān ge rén* 'three people'. -/
def ge : Classifier := { toMorph := .free "gè", script := some "个" }

/-- *wèi* 位, the polite counterpart of *gè* for persons: *xiānsheng* 'gentleman'. -/
def wei : Classifier := { toMorph := .free "wèi", script := some "位" }

/-- *zhī* 只: *shǒu* 'hand', *gǒu* 'dog'. -/
def zhi : Classifier := { toMorph := .free "zhī", script := some "只" }

/-- *jiàn* 件: *yīfu* 'garment'. -/
def jian : Classifier := { toMorph := .free "jiàn", script := some "件" }

/-- *duǒ* 朵: *huā* 'flower'. -/
def duo : Classifier := { toMorph := .free "duǒ", script := some "朵" }

/-- *jià* 架: *fēijī* 'airplane'. -/
def jia : Classifier := { toMorph := .free "jià", script := some "架" }

/-- *liàng* 辆: *chē* 'vehicle'. -/
def liang : Classifier := { toMorph := .free "liàng", script := some "辆" }

/-- *zhǎn* 盏: *dēng* 'lamp'. -/
def zhan : Classifier := { toMorph := .free "zhǎn", script := some "盏" }

/-- *pǐ* 匹: *mǎ* 'horse'. -/
def pi : Classifier := { toMorph := .free "pǐ", script := some "匹" }

/-- *tóu* 头 'head': *niú* 'cattle'. -/
def tou : Classifier := { toMorph := .free "tóu", script := some "头" }

/-- *běn* 本 'volume': *shū* 'book' as a thing. -/
def ben : Classifier := { toMorph := .free "běn", script := some "本" }

/-- *bù* 部: *shū* 'book' as a work. -/
def bu : Classifier := { toMorph := .free "bù", script := some "部" }

/-- *zhāng* 张 'sheet': *chuáng* 'bed', *zhuōzi* 'table'. -/
def zhang : Classifier := { toMorph := .free "zhāng", script := some "张" }

/-- *bǎ* 把, of things taken hold of: *dāo* 'knife'. -/
def ba : Classifier := { toMorph := .free "bǎ", script := some "把" }

/-- *zhī* 枝 'branch': *máobǐ* 'brush-pen', *jiàn* 'arrow'. -/
def zhiBranch : Classifier := { toMorph := .free "zhī", script := some "枝" }

/-- *kē* 棵: *cǎo* 'grass', *huā* 'flower' as a plant. -/
def ke : Classifier := { toMorph := .free "kē", script := some "棵" }

/-- *tiáo* 条 'strip': *shé* 'snake', *hé* 'river', *niú* 'cow', *xīnwén* 'news'. -/
def tiao : Classifier := { toMorph := .free "tiáo", script := some "条" }

/-- *dào* 道 'way, course': *hé* 'river', *cài* 'course of food'. -/
def dao : Classifier := { toMorph := .free "dào", script := some "道" }

/-- *mén* 门: *dàpào* 'artillery piece'. -/
def men : Classifier := { toMorph := .free "mén", script := some "门" }

/-- *xiē* 些, the classifier of plurality, 'several' after *yī* 'one': *yī xiē wánjù* 'some
toys'. -/
def xie : Classifier := { toMorph := .free "xiē", script := some "些", gloss := "PL" }

/-- The individual classifiers. -/
def classifiers : Finset Classifier :=
  {ge, wei, zhi, jian, duo, jia, liang, zhan, pi, tou, ben, bu, zhang, ba, zhiBranch, ke, tiao,
    dao, men, xie}

/-! ### Container measures -/

/-- *píng* 瓶 'bottle': *yóu* 'oil', *cù* 'vinegar'. -/
def ping : Classifier := { toMorph := .free "píng", script := some "瓶", gloss := "bottle" }

/-- *bēi* 杯 'glass, cup': *jiǔ* 'wine', *chá* 'tea'. -/
def bei : Classifier := { toMorph := .free "bēi", script := some "杯", gloss := "glass" }

/-- *xiāng* 箱 'box, chest': *júzi* 'orange'. -/
def xiang : Classifier := { toMorph := .free "xiāng", script := some "箱", gloss := "box" }

/-- *hé* 盒 'small box': *táng* 'candy'. -/
def he : Classifier := { toMorph := .free "hé", script := some "盒", gloss := "box" }

/-- *guō* 锅 'pot': *fàn* 'cooked rice'. -/
def guo : Classifier := { toMorph := .free "guō", script := some "锅", gloss := "pot" }

/-- *gāng* 缸 'vat': *cù* 'vinegar'. -/
def gang : Classifier := { toMorph := .free "gāng", script := some "缸", gloss := "vat" }

/-- *wǎn* 碗 'bowl': *fàn* 'cooked rice'. -/
def wan : Classifier := { toMorph := .free "wǎn", script := some "碗", gloss := "bowl" }

/-- The container measures, examples of an open class. -/
def containerMeasures : Finset Classifier := {ping, bei, xiang, he, guo, gang, wan}

end Mandarin.Classifiers
