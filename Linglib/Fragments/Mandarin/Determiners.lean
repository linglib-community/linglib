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
and *quánbù* 'all'. Words that mean the same differ in what may follow them and in whether they
need the adverb *dōu*. *Měi* must be followed by a classifier, as numerals and demonstratives
must, *hěnduō* may be, and the other words stand directly before the noun. A preverbal phrase
with *měi*, *suǒyǒu*, *quánbù* or *dàbùfèn* needs *dōu* before the verb, as in *suǒyǒu shīrén
dōu zuò báirìmèng* 'all poets daydream', and one with *hěnduō* admits it. The existential verb
*yǒu* introduces the cardinal phrases and not the universal ones.

## Implementation notes

* Each quantifier denotes the set of generalized-quantifier readings available for it, which is
  empty for *hěnduō*, whose standard is left to context.
* On Tsai's analysis *suǒyǒu*, *quánbù* and *dàbùfèn* are not determiners but introduce sets of
  alternatives that *dōu* closes. That reading lives at another type and is not among the sets
  recorded here.

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

namespace Mandarin.Determiners

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

/-! ### The classifier -/

/-- The word may stand before a classifier, as in *měi-liàng chē* 'every car' and *hěnduō-tiáo
kùzi* 'many pairs of pants'. The others may not, as in the ill-formed *\*suǒyǒu-ge xuéshēng*,
*\*yīxiē-pǐ mǎ* and *\*duōshù-ge xiǎohái* ([kuo-yu-2012]). No source stars *dàbùfèn* before a
classifier. It is entered with the others because its *bùfèn* 'part' is itself a partitive
measure in [chao-1968]'s list, as the *xiē* of *yīxiē* is, and [tsai-2015] likens both *bùfèn*
and the *shù* 'quantity' of *duōshù* to quantity-denoting classifiers, so the measure position
of these words is filled. -/
def TakesClassifier : QuantityWord → Prop
  | .mei | .henduo => True
  | _ => False

/-- The word may stand before the noun with no classifier between them, as in *hěnduō
yìngzhēngzhě* 'many applicants' and *suǒyǒu shīrén* 'all poets'. *Měi* may not, *\*měi chē*,
the noun *rén* 'person' apart. [kuo-yu-2012] star *hěnduō kùzi* in their survey of classifiers
and give *hěnduō* before a bare noun elsewhere, as does [tsai-2015]. -/
def TakesBareNoun : QuantityWord → Prop
  | .mei => False
  | _ => True

instance : DecidablePred TakesClassifier := fun w ↦ by
  unfold TakesClassifier; cases w <;> infer_instance

instance : DecidablePred TakesBareNoun := fun w ↦ by
  unfold TakesBareNoun; cases w <;> infer_instance

/-- The word needs a classifier, as [li-thompson-1981] say of *měi*. -/
def RequiresClassifier (w : QuantityWord) : Prop := w.TakesClassifier ∧ ¬ w.TakesBareNoun

/-- The word cannot precede a classifier. -/
def ExcludesClassifier (w : QuantityWord) : Prop := ¬ w.TakesClassifier ∧ w.TakesBareNoun

instance : DecidablePred RequiresClassifier := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

instance : DecidablePred ExcludesClassifier := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- Every word combines with a noun one way or the other. -/
theorem takesClassifier_or_takesBareNoun (w : QuantityWord) :
    w.TakesClassifier ∨ w.TakesBareNoun := by decide +revert

theorem requiresClassifier_iff {w : QuantityWord} : w.RequiresClassifier ↔ w = .mei := by
  decide +revert

/-- *Hěnduō* alone takes both a classifier and a bare noun. -/
theorem takesClassifier_and_takesBareNoun_iff {w : QuantityWord} :
    w.TakesClassifier ∧ w.TakesBareNoun ↔ w = .henduo := by decide +revert

theorem excludesClassifier_iff {w : QuantityWord} :
    w.ExcludesClassifier ↔ w ≠ .mei ∧ w ≠ .henduo := by decide +revert

/-! ### The adverb *dōu* -/

/-- A preverbal phrase headed by the word needs *dōu* before the verb, as in *{měi-ge,
suǒyǒu-de, dàbùfèn-de} rén \*(dōu) mǎi-le shū* 'every person, all people, most people bought a
book', against *hěnduō rén (dōu) mǎi-le shū* 'many people bought a book' ([tsai-2015]) and
*duōshù shīrén huì zuò báirìmèng* 'most poets daydream' ([kuo-yu-2012]). -/
def RequiresDou : QuantityWord → Prop
  | .mei | .suoyou | .quanbu | .dabufen => True
  | _ => False

instance : DecidablePred RequiresDou := fun w ↦ by unfold RequiresDou; cases w <;> infer_instance

/-! ### The available readings -/

universe u

/-- The readings available for a word, as generalized quantifiers on every finite domain.
*Yīxiē* reads as `Quantifier.GQ.some`, *méiyǒu* as `no`, *shǎoshù* as `few`, *duōshù* and
*dàbùfèn* as `most`, and *měi*, *suǒyǒu* and *quánbù* as `every`; *hěnduō* has no reading,
its standard being a value judgment left to context ([kuo-yu-2012]). Speakers judging
*dàbùfèn* accept its majority reading far more often than a relative one ([wang-2012]). -/
noncomputable instance : Semantics.Denotes QuantityWord (Set Quantifier.GQ.Family.{u}) where
  denote
    | .yixie => {Quantifier.GQ.Family.some}
    | .meiyou => {Quantifier.GQ.Family.no}
    | .shaoshu => {Quantifier.GQ.Family.few}
    | .duoshu | .dabufen => {Quantifier.GQ.Family.most}
    | .mei | .suoyou | .quanbu => {Quantifier.GQ.Family.every}
    | .henduo => ∅

end QuantityWord

/-! ## Demonstratives and the possessive -/

/-- *zhè* 这 'this', the proximal demonstrative, which stands before a classifier. -/
def zhe : DemonstrativeDeterminer := { form := "zhè", deixis := Person.first.participantSets }

/-- *nà* 那 'that', the distal demonstrative and the obligatory exponent of anaphoric definites,
donkey anaphora included ([jenks-2018]). -/
def na : DemonstrativeDeterminer :=
  { form := "nà", deixis := Person.first.participantSetsᶜ, uses := {.anaphoric} }

/-- *de* 的, the marker of possession and of nominal modification. -/
def de : PossessiveDeterminer := { form := "de" }

/-- The determiner inventory holds the demonstratives, the quantifiers and the possessive
marker, there being no articles. -/
def inventory : Determiner.Inventory :=
  [.demonstrative zhe, .demonstrative na] ++
    QuantityWord.toList.map (.quantifier ·.toQuantifier) ++ [.possessive de]

/-- Mandarin's inventory derives the `.markedAnaphoric` cell of [moroney-2021]: only the
demonstrative marks a definite use, and the use it marks is the anaphoric one. -/
theorem marking : inventory.markingStrategy = .markedAnaphoric := by decide

end Mandarin.Determiners
