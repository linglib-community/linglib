module

public import Linglib.Syntax.Category.Auxiliary.Basic

/-!
# Mandarin auxiliary verbs

This file defines the commonly used Mandarin auxiliary verbs of Li and Thompson's list:
*yīnggāi*, *yīngdāng* and *gāi* 'ought to, should'; *néng*, *nénggòu*, *huì* and *kěyǐ* 'be able
to'; *néng* and *kěyǐ* 'have permission to'; *gǎn* 'dare'; *kěn* 'be willing to'; *děi*, *bìxū*,
*bìyào* and *bìděi* 'must, ought to'; and *huì* 'will, know how'. An auxiliary, like a verb, can
be the A of an A-not-A question and can answer a question on its own, as in *wǒ néng* 'I can';
adverbs such as *yídìng* 'definitely' and *dàgài* 'approximately' can do neither.

## Implementation notes

The senses are read as flavors in the usual way: ability as circumstantial, and permission and
obligation as deontic. 'Ought to, should' is weak necessity, and the group glossed 'must, ought
to' is entered with necessity, the stronger of its two glosses. Senses that are not flavors are
left out: the future *huì* 'will', and the daring and willingness of *gǎn* and *kěn*, which are
auxiliaries without modality.

## References

* [li-thompson-1981]
* [kratzer-1981]
-/

@[expose] public section

namespace Mandarin.Auxiliaries

/-- *yīnggāi* 应该 'ought to, should'. -/
def yinggai : Auxiliary where
  form := "yīnggāi"
  meaning := {.weakNecessity} ×ˢ {.deontic}

/-- *yīngdāng* 应当 'ought to, should'. -/
def yingdang : Auxiliary where
  form := "yīngdāng"
  meaning := {.weakNecessity} ×ˢ {.deontic}

/-- *gāi* 该 'ought to, should'. -/
def gai : Auxiliary where
  form := "gāi"
  meaning := {.weakNecessity} ×ˢ {.deontic}

/-- *néng* 能 'be able to', 'have permission to'. -/
def neng : Auxiliary where
  form := "néng"
  meaning := {.possibility} ×ˢ {.circumstantial, .deontic}

/-- *nénggòu* 能够 'be able to'. -/
def nenggou : Auxiliary where
  form := "nénggòu"
  meaning := {.possibility} ×ˢ {.circumstantial}

/-- *huì* 会 'be able to, know how'; its sense 'will' is not a flavor. -/
def hui : Auxiliary where
  form := "huì"
  meaning := {.possibility} ×ˢ {.circumstantial}

/-- *kěyǐ* 可以 'be able to', 'have permission to'. -/
def keyi : Auxiliary where
  form := "kěyǐ"
  meaning := {.possibility} ×ˢ {.circumstantial, .deontic}

/-- *gǎn* 敢 'dare'. -/
def gan : Auxiliary where
  form := "gǎn"

/-- *kěn* 肯 'be willing to'. -/
def ken : Auxiliary where
  form := "kěn"

/-- *děi* 得 'must, ought to'. -/
def dei : Auxiliary where
  form := "děi"
  meaning := {.necessity} ×ˢ {.deontic}

/-- *bìxū* 必须 'must, ought to'. -/
def bixu : Auxiliary where
  form := "bìxū"
  meaning := {.necessity} ×ˢ {.deontic}

/-- *bìyào* 必要 'must, ought to'. -/
def biyao : Auxiliary where
  form := "bìyào"
  meaning := {.necessity} ×ˢ {.deontic}

/-- *bìděi* 必得 'must, ought to'. -/
def bidei : Auxiliary where
  form := "bìděi"
  meaning := {.necessity} ×ˢ {.deontic}

/-- The auxiliary verbs. -/
def auxiliaries : List Auxiliary :=
  [yinggai, yingdang, gai, neng, nenggou, hui, keyi, gan, ken, dei, bixu, biyao, bidei]

/-- The modal auxiliaries, those with a modality. -/
def modals : List Auxiliary := auxiliaries.filter (·.meaning.Nonempty)

end Mandarin.Auxiliaries
