module

public import Linglib.Syntax.Category.Noun.Basic
public import Linglib.Fragments.Japanese.Classifiers

/-!
# Japanese nouns

The Japanese noun as a lexical entry: the root entry with its romanization as citation form, its
spelling, the ways a numeral counts it, and the optional plural in *-tachi* where the entry records
one; a name is the root `ProperName` with its spelling. Japanese has no articles, and a bare noun
can be an argument. No numeral counts a mass noun such as *mizu* 'water', with or without a
classifier.

## References

* [downing-1996]
-/

@[expose] public section

namespace Japanese.Nouns

/-- A Japanese noun is the root entry with its romanization as citation form, its spelling, the
ways a numeral counts it, and its optional plural. -/
structure Noun extends ClassifiedNoun Classifier where
  /-- The spelling in kanji and kana. -/
  script : String
  /-- The optional plural in *-tachi*, romanized. -/
  plural : Option String := none
  deriving DecidableEq

/-! ### Common nouns -/

/-- 犬 *inu* 'dog'. -/
def inu : Noun :=
  { form := "inu", script := "犬", gloss := "dog", counters := {some Classifiers.hiki} }

/-- 猫 *neko* 'cat'. -/
def neko : Noun :=
  { form := "neko", script := "猫", gloss := "cat", counters := {some Classifiers.hiki} }

/-- 人 *hito* 'person'. -/
def hito : Noun :=
  { form := "hito", script := "人", gloss := "person", counters := {some Classifiers.nin},
    plural := "hitotachi" }

/-- 本 *hon* 'book'. -/
def hon : Noun :=
  { form := "hon", script := "本", gloss := "book", counters := {some Classifiers.satsu} }

/-- 車 *kuruma* 'car'. -/
def kuruma : Noun :=
  { form := "kuruma", script := "車", gloss := "car", counters := {some Classifiers.dai} }

/-- 鳥 *tori* 'bird'. -/
def tori : Noun :=
  { form := "tori", script := "鳥", gloss := "bird", counters := {some Classifiers.wa} }

/-- 花 *hana* 'flower'. -/
def hana : Noun :=
  { form := "hana", script := "花", gloss := "flower", counters := {some Classifiers.hon} }

/-- 水 *mizu* 'water'. -/
def mizu : Noun := { form := "mizu", script := "水", gloss := "water", counters := ∅ }

/-- ご飯 *gohan* 'cooked rice'. -/
def gohan : Noun := { form := "gohan", script := "ご飯", gloss := "cooked rice", counters := ∅ }

/-- 娘 *musume* 'daughter'. -/
def musume : Noun :=
  { form := "musume", script := "娘", gloss := "daughter", counters := {some Classifiers.nin},
    plural := "musumetachi" }

/-- 息子 *musuko* 'son'. -/
def musuko : Noun :=
  { form := "musuko", script := "息子", gloss := "son", counters := {some Classifiers.nin},
    plural := "musukotachi" }

/-- 学生 *gakusei* 'student'. -/
def gakusei : Noun :=
  { form := "gakusei", script := "学生", gloss := "student", counters := {some Classifiers.nin},
    plural := "gakuseitachi" }

/-- 先生 *sensei* 'teacher'. -/
def sensei : Noun :=
  { form := "sensei", script := "先生", gloss := "teacher", counters := {some Classifiers.nin},
    plural := "senseitachi" }

/-- 友達 *tomodachi* 'friend'. -/
def tomodachi : Noun :=
  { form := "tomodachi", script := "友達", gloss := "friend", counters := {some Classifiers.nin} }

/-- The nouns. -/
def nouns : List Noun :=
  [inu, neko, hito, hon, kuruma, tori, hana, mizu, gohan, musume, musuko, gakusei, sensei,
    tomodachi]

/-! ### Proper names -/

/-- A Japanese name is the root name with its romanization as citation form, and its spelling. -/
structure ProperName extends _root_.ProperName where
  /-- The spelling in kanji and kana. -/
  script : String
  deriving DecidableEq, Repr

/-- A personal name glossed by its romanization. -/
def name (form script : String) (gender : Option Gender.Label := none) : ProperName :=
  { form, gloss := form, script, gender }

def taro : ProperName := name "Tarō" "太郎" (some .masculine)
def hanako : ProperName := name "Hanako" "花子" (some .feminine)
def yamada : ProperName := name "Yamada" "山田"
def tanaka : ProperName := name "Tanaka" "田中"

end Japanese.Nouns
