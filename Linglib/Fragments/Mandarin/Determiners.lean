module

public import Linglib.Semantics.Quantification.Determiner

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

/-- A Mandarin quantificational determiner, with its characters, whether it may stand before a
classifier or directly before the noun, and whether a preverbal phrase it heads needs the adverb
*dōu*. No word restricts number, and the words that take a bare noun take a count or a mass noun
alike, as in *suǒyǒu de zhūròu* 'all the pork' beside *suǒyǒu de zhū* 'all the pigs'
([kuo-yu-2012]). -/
structure QuantityWord extends QuantificationalDeterminer where
  /-- The characters. -/
  hanzi : String
  /-- The word may stand before a classifier. -/
  takesClassifier : Bool
  /-- The word may stand before the noun with no classifier between them. -/
  takesBareNoun : Bool
  /-- A preverbal phrase headed by the word needs *dōu* before the verb. -/
  requiresDou : Bool
  deriving DecidableEq

namespace QuantityWord

attribute [coe] QuantityWord.toQuantificationalDeterminer

instance : CoeOut QuantityWord QuantificationalDeterminer := ⟨toQuantificationalDeterminer⟩

/-- A word denotes the readings of its record. -/
noncomputable instance : Denotes QuantityWord (Set Det.Family.{u}) where
  denote w := ⟦(w : QuantificationalDeterminer)⟧

/-- The word may stand before a classifier, as in *měi-liàng chē* 'every car' and *hěnduō-tiáo
kùzi* 'many pairs of pants', and the others may not, as in *\*suǒyǒu-ge xuéshēng*, *\*yīxiē-pǐ
mǎ* and *\*duōshù-ge xiǎohái* ([kuo-yu-2012]). -/
def TakesClassifier (w : QuantityWord) : Prop := w.takesClassifier = true

/-- The word may stand before the noun with no classifier between them, as in *hěnduō
yìngzhēngzhě* 'many applicants' and *suǒyǒu shīrén* 'all poets', which *měi* may not, *\*měi
chē*, the noun *rén* 'person' apart ([kuo-yu-2012], [li-thompson-1981]). -/
def TakesBareNoun (w : QuantityWord) : Prop := w.takesBareNoun = true

/-- A preverbal phrase headed by the word needs *dōu* before the verb, as in *měi-ge xuéshēng
\*(dōu) xiě-le yī-shǒu shī* 'every student wrote a poem' ([kuo-yu-2012]), against *hěnduō rén
(dōu) mǎi-le shū* 'many people bought a book' ([tsai-2015]). -/
def RequiresDou (w : QuantityWord) : Prop := w.requiresDou = true

instance : DecidablePred TakesClassifier := fun _ ↦ inferInstanceAs (Decidable (_ = _))

instance : DecidablePred TakesBareNoun := fun _ ↦ inferInstanceAs (Decidable (_ = _))

instance : DecidablePred RequiresDou := fun _ ↦ inferInstanceAs (Decidable (_ = _))

end QuantityWord

/-- *Yīxiē* 'some', read as `Quantifier.Det.some`. -/
def yixie : QuantityWord :=
  { form := "yīxiē", hanzi := "一些", readings := {.some}, selectsMass := true,
    takesClassifier := false, takesBareNoun := true, requiresDou := false }

/-- *Méiyǒu* 'no', read as `no`. -/
def meiyou : QuantityWord :=
  { form := "méiyǒu", hanzi := "没有", readings := {.no}, selectsMass := true,
    takesClassifier := false, takesBareNoun := true, requiresDou := false }

/-- *Hěnduō* 'many', with no reading, its standard being a value judgment left to context
([kuo-yu-2012]). -/
def henduo : QuantityWord :=
  { form := "hěnduō", hanzi := "很多", selectsMass := true,
    takesClassifier := true, takesBareNoun := true, requiresDou := false }

/-- *Shǎoshù* 'a minority of', read as `few`. -/
def shaoshu : QuantityWord :=
  { form := "shǎoshù", hanzi := "少数", readings := {.few}, selectsMass := true,
    takesClassifier := false, takesBareNoun := true, requiresDou := false }

/-- *Duōshù* 'most', read as `most`. -/
def duoshu : QuantityWord :=
  { form := "duōshù", hanzi := "多数", readings := {.most}, selectsMass := true,
    takesClassifier := false, takesBareNoun := true, requiresDou := false }

/-- *Dàbùfèn* 'most', read as `most`; speakers judging it accept its majority reading far more
often than a relative one ([wang-2012], §4.2.2.2). -/
def dabufen : QuantityWord :=
  { form := "dàbùfèn", hanzi := "大部分", readings := {.most}, selectsMass := true,
    takesClassifier := false, takesBareNoun := true, requiresDou := false }

/-- *Měi* 'every', read as `every`. -/
def mei : QuantityWord :=
  { form := "měi", hanzi := "每", readings := {.every}, selectsMass := true,
    takesClassifier := true, takesBareNoun := false, requiresDou := true }

/-- *Suǒyǒu* 'all', read as `every`. -/
def suoyou : QuantityWord :=
  { form := "suǒyǒu", hanzi := "所有", readings := {.every}, selectsMass := true,
    takesClassifier := false, takesBareNoun := true, requiresDou := true }

/-- *Quánbù* 'all', read as `every`. -/
def quanbu : QuantityWord :=
  { form := "quánbù", hanzi := "全部", readings := {.every}, selectsMass := true,
    takesClassifier := false, takesBareNoun := true, requiresDou := true }

/-- The quantificational determiners. -/
def quantityWords : List QuantityWord :=
  [yixie, meiyou, henduo, shaoshu, duoshu, dabufen, mei, suoyou, quanbu]

namespace QuantityWord

/-- Whether a word takes a classifier is not a function of its readings: *měi* and *suǒyǒu*
both read as `every`, and only *měi* takes one ([kuo-yu-2012], p. 666). -/
theorem not_factorsThrough_takesClassifier :
    ¬ Function.FactorsThrough TakesClassifier fun w ↦ (⟦w⟧ : Set Det.Family.{u}) :=
  fun h ↦ absurd ((h (a := mei) (b := suoyou) rfl).mp rfl) (by decide)

/-- A word needs *dōu* exactly when its one reading is `every`, *dōu* being obligatory in basic
universal quantification ([kuo-yu-2012], p. 655). -/
theorem requiresDou_iff : ∀ w ∈ quantityWords,
    w.RequiresDou ↔ ⟦w⟧ = ({Det.Family.every} : Set Det.Family.{u}) := by
  simp only [quantityWords, List.mem_cons, List.not_mem_nil, or_false]
  rintro w (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp [RequiresDou, Denotes.denote, yixie, meiyou, henduo, shaoshu, duoshu, dabufen, mei,
      suoyou, quanbu, Det.Family.some_ne_every,
      Det.Family.no_ne_every, Det.Family.most_ne_every, Det.Family.few_ne_every]

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
    quantityWords.map (.quantifier ·.toQuantificationalDeterminer) ++ [.possessive de]

end Mandarin.Determiners
