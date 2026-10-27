module

public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Denotation

/-!
# Mandarin determiners

Mandarin has no articles. A bare noun serves as a unique definite, an anaphoric definite needs
the demonstrative *nà* 'that', in donkey sentences too, and possession is marked with *de*. The
quantifiers are cardinal, *yīxiē* 'some', *méiyǒu* 'no' and *hěnduō* 'many', proportional,
*shǎoshù* 'a minority of', *duōshù* and *dàbùfèn* 'most', or universal, *měi* 'every', *suǒyǒu*
and *quánbù* 'all'. Words that mean the same differ in what may follow them: *měi* must be
followed by a classifier, as numerals and demonstratives must, *hěnduō* may be, and the other
words stand directly before the noun. Whether a word needs the adverb *dōu* follows its meaning
instead. A preverbal phrase with a universal word needs *dōu* before the verb, as in *suǒyǒu
shīrén dōu zuò báirìmèng* 'all poets daydream', and one with *hěnduō* admits it. The existential
verb *yǒu* introduces phrases with *yīxiē*, *hěnduō* and *shǎoshù* and not the universal ones.

## Main results

* `Mandarin.Determiners.QuantityWord.requiresDou_iff`: a word needs *dōu* exactly when it reads
  as `every`.
* `Mandarin.Determiners.QuantityWord.not_factorsThrough_takesClassifier`: whether a word takes a
  classifier is not a function of its readings.

## Implementation notes

* Each quantifier denotes the set of generalized-quantifier readings available for it, which is
  empty for *hěnduō*, whose standard is left to context.
* Speakers differ over *dōu* with *dàbùfèn*: Lin has it obligatory and Chen optional, both as
  cited by Tsai, and Kuo and Yu find *dōu* optional with proportional quantifiers, so *dàbùfèn* is
  entered as not needing it. Kuo and Yu's *duōshù shīrén huì zuò báirìmèng* 'most poets
  daydream' has no *dōu* after the modal *huì*, which lets even a phrase with *měi* drop it (Cao,
  as cited by Tsai).
* No source stars *dàbùfèn* before a classifier. It is entered with the words that take none
  since its *bùfèn* 'part' is itself a partitive measure for Chao, as the *xiē* of *yīxiē* is,
  which Li and Thompson count a classifier and `Mandarin.Classifiers` enters as one.
* On Tsai's analysis *suǒyǒu*, *quánbù* and *dàbùfèn* are not determiners but introduce sets of
  alternatives that *dōu* closes. That reading lives at another type and is not among the sets
  recorded here.

## Errata

* Kuo and Yu state that the generalized existential quantifiers other than *yīxiē* and
  *méiyǒu* require a classifier (p. 666), but give *hěnduō yìngzhēngzhě* 'many applicants' in
  (3a) and *yǒu hěnduō xuéshēng* 'there are many students' in (26a).

## References

* [kuo-yu-2012]
* [tsai-2015]
* [li-thompson-1981]
* [chao-1968]
* [wang-2012]
* [jenks-2018]
* [moroney-2021]
-/

@[expose] public section

universe u

namespace Mandarin.Determiners

open Quantifier
open scoped Denotes

/-! ## Quantificational determiners -/

/-- The quantificational determiners of Mandarin are the cardinal *yīxiē* 'some', *méiyǒu* 'no'
and *hěnduō* 'many', the proportional *shǎoshù* 'a minority of', *duōshù* 'most' and *dàbùfèn*
'most', and the universal *měi* 'every', *suǒyǒu* 'all' and *quánbù* 'all'. -/
inductive QuantityWord where
  | yixie | meiyou | henduo | shaoshu | duoshu | dabufen | mei | suoyou | quanbu
  deriving DecidableEq, Repr, Fintype

namespace QuantityWord

/-- The pinyin form. -/
def form : QuantityWord → String
  | .yixie => "yīxiē"
  | .meiyou => "méiyǒu"
  | .henduo => "hěnduō"
  | .shaoshu => "shǎoshù"
  | .duoshu => "duōshù"
  | .dabufen => "dàbùfèn"
  | .mei => "měi"
  | .suoyou => "suǒyǒu"
  | .quanbu => "quánbù"

/-- The characters. -/
def hanzi : QuantityWord → String
  | .yixie => "一些"
  | .meiyou => "没有"
  | .henduo => "很多"
  | .shaoshu => "少数"
  | .duoshu => "多数"
  | .dabufen => "大部分"
  | .mei => "每"
  | .suoyou => "所有"
  | .quanbu => "全部"

/-- The word as a determiner record. No word restricts number, and the words that take a bare
noun take a count or a mass noun alike, as in *suǒyǒu de zhūròu* 'all the pork' beside *suǒyǒu de
zhū* 'all the pigs' ([kuo-yu-2012]). -/
def toQuantifier (w : QuantityWord) : Quantifier := { form := w.form, selectsMass := true }

/-- All the words. -/
def toList : List QuantityWord :=
  [.yixie, .meiyou, .henduo, .shaoshu, .duoshu, .dabufen, .mei, .suoyou, .quanbu]

theorem mem_toList (w : QuantityWord) : w ∈ toList := by cases w <;> decide

/-- The readings available for a word, as generalized quantifiers on every finite domain.
*Yīxiē* reads as `Quantifier.GQ.some`, *méiyǒu* as `no`, *shǎoshù* as `few`, *duōshù* and
*dàbùfèn* as `most`, and *měi*, *suǒyǒu* and *quánbù* as `every`; *hěnduō* has no reading,
its standard being a value judgment left to context ([kuo-yu-2012]). Speakers judging
*dàbùfèn* accept its majority reading far more often than a relative one ([wang-2012],
§4.2.2.2). -/
noncomputable instance : Denotes QuantityWord (Set GQ.Family.{u}) where
  denote
    | .yixie => {GQ.Family.some}
    | .meiyou => {GQ.Family.no}
    | .shaoshu => {GQ.Family.few}
    | .duoshu | .dabufen => {GQ.Family.most}
    | .mei | .suoyou | .quanbu => {GQ.Family.every}
    | .henduo => ∅

/-! ### The classifier -/

/-- The word may stand before a classifier, as in *měi-liàng chē* 'every car' and *hěnduō-tiáo
kùzi* 'many pairs of pants', and the others may not, as in *\*suǒyǒu-ge xuéshēng*, *\*yīxiē-pǐ
mǎ* and *\*duōshù-ge xiǎohái* ([kuo-yu-2012]). -/
def TakesClassifier : QuantityWord → Prop
  | .mei | .henduo => True
  | _ => False

/-- The word may stand before the noun with no classifier between them, as in *hěnduō
yìngzhēngzhě* 'many applicants' and *suǒyǒu shīrén* 'all poets', which *měi* may not, *\*měi
chē*, the noun *rén* 'person' apart ([kuo-yu-2012], [li-thompson-1981]). -/
def TakesBareNoun : QuantityWord → Prop
  | .mei => False
  | _ => True

instance : DecidablePred TakesClassifier := fun w ↦ by
  unfold TakesClassifier; cases w <;> infer_instance

instance : DecidablePred TakesBareNoun := fun w ↦ by
  unfold TakesBareNoun; cases w <;> infer_instance

/-- Whether a word takes a classifier is not a function of its readings: *měi* and *suǒyǒu*
both read as `every`, and only *měi* takes one ([kuo-yu-2012], p. 666). -/
theorem not_factorsThrough_takesClassifier :
    ¬ Function.FactorsThrough TakesClassifier fun w ↦ (⟦w⟧ : Set GQ.Family.{u}) :=
  fun h ↦ (h (a := .mei) (b := .suoyou) rfl).mp trivial

/-! ### The adverb *dōu* -/

/-- A preverbal phrase headed by the word needs *dōu* before the verb, as in *měi-ge xuéshēng
\*(dōu) xiě-le yī-shǒu shī* 'every student wrote a poem' ([kuo-yu-2012]), against *hěnduō rén
(dōu) mǎi-le shū* 'many people bought a book' ([tsai-2015]). -/
def RequiresDou : QuantityWord → Prop
  | .mei | .suoyou | .quanbu => True
  | _ => False

instance : DecidablePred RequiresDou := fun w ↦ by unfold RequiresDou; cases w <;> infer_instance

/-- A word needs *dōu* exactly when its one reading is `every`, *dōu* being obligatory in basic
universal quantification ([kuo-yu-2012], p. 655). -/
theorem requiresDou_iff {w : QuantityWord} :
    w.RequiresDou ↔ ⟦w⟧ = ({GQ.Family.every} : Set GQ.Family.{u}) := by
  cases w <;> simp [RequiresDou, Denotes.denote, GQ.Family.some_ne_every, GQ.Family.no_ne_every,
    GQ.Family.most_ne_every, GQ.Family.few_ne_every]

end QuantityWord

/-! ## Demonstratives and the possessive -/

/-- *zhè* 这 'this', the proximal demonstrative, which stands before a classifier. -/
def zhe : DemonstrativeDeterminer := { form := "zhè", deixis := Person.first.participantSets }

/-- *nà* 那 'that', the distal demonstrative, which [jenks-2018] finds required in anaphoric
definites outside a continuing topic, donkey anaphora and producer–product bridging included. -/
def na : DemonstrativeDeterminer := { form := "nà", deixis := Person.first.participantSetsᶜ }

/-- *de* 的, the marker of possession and of nominal modification. -/
def de : PossessiveDeterminer := { form := "de" }

/-- The determiner inventory holds the demonstratives, the quantifiers and the possessive
marker, there being no articles. -/
def inventory : Determiner.Inventory :=
  [.demonstrative zhe, .demonstrative na] ++
    QuantityWord.toList.map (.quantifier ·.toQuantifier) ++ [.possessive de]

end Mandarin.Determiners
