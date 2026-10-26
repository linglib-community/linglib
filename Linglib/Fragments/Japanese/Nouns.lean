module

public import Linglib.Syntax.Category.Noun.Basic
public import Linglib.Semantics.Reference.Animacy
public import Linglib.Fragments.Japanese.Classifiers

/-!
# Japanese nouns

The Japanese noun as a lexical entry: the root entry with its romanization as citation form, its
spelling, the ways a numeral counts it, and the animacy of its referents; a name is the root
`ProperName` with its spelling. Japanese has no articles, and a bare noun can be an argument.
Every noun entered here is counted through a classifier, a liquid in drops with *-teki*, which
Downing keeps among the classifiers because a drop is a natural unit of the liquid, and cooked rice
in grains with *-tsubu*. The plural suffix *-tachi* is not entered on the nouns: whether a common
noun takes it depends on the animacy of its referents.

## Main definitions

* `Japanese.Nouns.Noun`, `Japanese.Nouns.nouns`: the noun entry and the common nouns entered here.
* `Japanese.Nouns.ProperName`, `Japanese.Nouns.name`: the entry of a name.

## References

* [downing-1996]
-/

@[expose] public section

namespace Japanese.Nouns

/-- A Japanese noun is the root entry with its romanization as citation form, its spelling, the
ways a numeral counts it, and the animacy of its referents. -/
structure Noun extends ClassifiedNoun Classifier where
  /-- The spelling in kanji and kana. -/
  script : String
  /-- The animacy of the noun's referents. -/
  animacy : Animacy
  deriving DecidableEq

/-! ### Common nouns -/

/-- 犬 *inu* 'dog'. -/
def inu : Noun :=
  { form := "inu", script := "犬", gloss := "dog", counters := {some Classifiers.hiki},
    animacy := .animate }

/-- 猫 *neko* 'cat'. -/
def neko : Noun :=
  { form := "neko", script := "猫", gloss := "cat", counters := {some Classifiers.hiki},
    animacy := .animate }

/-- 人 *hito* 'person'. -/
def hito : Noun :=
  { form := "hito", script := "人", gloss := "person", counters := {some Classifiers.nin},
    animacy := .human }

/-- 子供 *kodomo* 'child'. -/
def kodomo : Noun :=
  { form := "kodomo", script := "子供", gloss := "child", counters := {some Classifiers.nin},
    animacy := .human }

/-- 本 *hon* 'book'. -/
def hon : Noun :=
  { form := "hon", script := "本", gloss := "book", counters := {some Classifiers.satsu},
    animacy := .inanimate }

/-- 車 *kuruma* 'car'. -/
def kuruma : Noun :=
  { form := "kuruma", script := "車", gloss := "car", counters := {some Classifiers.dai},
    animacy := .inanimate }

/-- 建物 *tatemono* 'building'. -/
def tatemono : Noun :=
  { form := "tatemono", script := "建物", gloss := "building",
    counters := {some Classifiers.kenBuilding, some Classifiers.mune}, animacy := .inanimate }

/-- 鳥 *tori* 'bird', counted with *-wa*, and with *-hiki* except by some speakers. -/
def tori : Noun :=
  { form := "tori", script := "鳥", gloss := "bird",
    counters := {some Classifiers.wa, some Classifiers.hiki}, animacy := .animate }

/-- 花 *hana* 'flower', counted by the stem with *-hon* and by the blossom with *-rin*. -/
def hana : Noun :=
  { form := "hana", script := "花", gloss := "flower",
    counters := {some Classifiers.hon, some Classifiers.rin}, animacy := .inanimate }

/-- 水 *mizu* 'water', counted in drops with *-teki* and *-tsubu*. -/
def mizu : Noun :=
  { form := "mizu", script := "水", gloss := "water",
    counters := {some Classifiers.teki, some Classifiers.tsubu}, animacy := .inanimate }

/-- ご飯 *gohan* 'cooked rice', counted in grains with *-tsubu* and in bowls with *-zen*. -/
def gohan : Noun :=
  { form := "gohan", script := "ご飯", gloss := "cooked rice",
    counters := {some Classifiers.tsubu, some Classifiers.zen}, animacy := .inanimate }

/-- 娘 *musume* 'daughter'. -/
def musume : Noun :=
  { form := "musume", script := "娘", gloss := "daughter", counters := {some Classifiers.nin},
    animacy := .human }

/-- 息子 *musuko* 'son'. -/
def musuko : Noun :=
  { form := "musuko", script := "息子", gloss := "son", counters := {some Classifiers.nin},
    animacy := .human }

/-- 学生 *gakusei* 'student'. -/
def gakusei : Noun :=
  { form := "gakusei", script := "学生", gloss := "student", counters := {some Classifiers.nin},
    animacy := .human }

/-- 先生 *sensei* 'teacher'. -/
def sensei : Noun :=
  { form := "sensei", script := "先生", gloss := "teacher", counters := {some Classifiers.nin},
    animacy := .human }

/-- 友達 *tomodachi* 'friend'. -/
def tomodachi : Noun :=
  { form := "tomodachi", script := "友達", gloss := "friend", counters := {some Classifiers.nin},
    animacy := .human }

/-- The nouns. -/
def nouns : List Noun :=
  [inu, neko, hito, kodomo, hon, kuruma, tatemono, tori, hana, mizu, gohan, musume, musuko,
    gakusei, sensei, tomodachi]

/-! ### Proper names -/

/-- A Japanese name is the root name with its romanization as citation form, and its spelling. -/
structure ProperName extends _root_.ProperName where
  /-- The spelling in kanji and kana. -/
  script : String
  deriving DecidableEq, Repr

/-- A personal name glossed by its romanization. -/
def name (form script : String) (referentGender : Option ReferentGender := none) : ProperName :=
  { form, gloss := form, script, referentGender }

/-- *Tarō* 太郎, a man's given name. -/
def taro : ProperName := name "Tarō" "太郎" (some .male)

/-- *Hanako* 花子, a woman's given name. -/
def hanako : ProperName := name "Hanako" "花子" (some .female)

/-- *Yamada* 山田, a family name. -/
def yamada : ProperName := name "Yamada" "山田"

/-- *Tanaka* 田中, a family name. -/
def tanaka : ProperName := name "Tanaka" "田中"

end Japanese.Nouns
