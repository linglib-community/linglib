module

public import Linglib.Syntax.Category.Noun.Basic
public import Linglib.Fragments.Mandarin.Classifiers

/-!
# Mandarin nouns

The Mandarin noun as a lexical entry: the root entry with the pinyin as citation form, its
characters, and the ways a numeral counts it; a name is the root `ProperName` with its characters.
Each noun has its own classifier, and a few have two according to their meaning, *shū* 'book' taking
*běn* as a thing and *bù* as a work; beside its own classifiers a noun can always be counted with
the general *gè* (`Noun.Takes`). A numeral counts a noun that denotes a measure, *tiān* 'day',
without a classifier, and no numeral counts a noun counted through measure words, *jiǔ* 'wine' or
*fàn* 'cooked rice', in either way. The entries are the pairings of noun and classifier that Li and
Thompson and Chao give.

## References

* [li-thompson-1981]
* [chao-1968]
-/

@[expose] public section

namespace Mandarin.Nouns

/-- A Mandarin noun is the root entry with the pinyin as citation form, its characters, and the
ways a numeral counts it. -/
structure Noun extends ClassifiedNoun Classifier where
  /-- The characters. -/
  hanzi : String
  deriving DecidableEq

/-- A noun can be counted with a classifier of its own, and with the general *gè* when it takes
a classifier at all. -/
def Noun.Takes (n : Noun) (c : Classifier) : Prop :=
  c ∈ n.classifiers ∨ c = Classifiers.ge ∧ n.classifiers.Nonempty

instance (n : Noun) (c : Classifier) : Decidable (n.Takes c) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem Noun.takes_ge {n : Noun} (h : n.classifiers.Nonempty) : n.Takes Classifiers.ge :=
  .inr ⟨rfl, h⟩

theorem Noun.not_takes_of_eq_empty {n : Noun} (h : n.classifiers = ∅) (c : Classifier) :
    ¬ n.Takes c := by
  simp [Noun.Takes, h]

/-! ### Nouns counted with *gè* alone -/

/-- 人 *rén* 'person'. -/
def ren : Noun :=
  { form := "rén", hanzi := "人", gloss := "person", counters := {some Classifiers.ge} }

/-- 问题 *wèntí* 'problem'. -/
def wenti : Noun :=
  { form := "wèntí", hanzi := "问题", gloss := "problem", counters := {some Classifiers.ge} }

/-! ### Nouns with a classifier of their own -/

/-- 先生 *xiānsheng* 'gentleman', counted with the polite *wèi*. -/
def xiansheng : Noun :=
  { form := "xiānsheng", hanzi := "先生", gloss := "gentleman", counters := {some Classifiers.wei} }

/-- 狗 *gǒu* 'dog', with *zhī* and, in some dialects, *tiáo*. -/
def gou : Noun :=
  { form := "gǒu", hanzi := "狗", gloss := "dog",
    counters := {some Classifiers.zhi, some Classifiers.tiao} }

/-- 手 *shǒu* 'hand'. -/
def shou : Noun :=
  { form := "shǒu", hanzi := "手", gloss := "hand", counters := {some Classifiers.zhi} }

/-- 衣服 *yīfu* 'garment'. -/
def yifu : Noun :=
  { form := "yīfu", hanzi := "衣服", gloss := "garment", counters := {some Classifiers.jian} }

/-- 花 *huā* 'flower', with *duǒ* for the blossom and *kē* for the plant. -/
def hua : Noun :=
  { form := "huā", hanzi := "花", gloss := "flower",
    counters := {some Classifiers.duo, some Classifiers.ke} }

/-- 草 *cǎo* 'grass'. -/
def cao : Noun :=
  { form := "cǎo", hanzi := "草", gloss := "grass", counters := {some Classifiers.ke} }

/-- 飞机 *fēijī* 'airplane'. -/
def feiji : Noun :=
  { form := "fēijī", hanzi := "飞机", gloss := "airplane", counters := {some Classifiers.jia} }

/-- 车 *chē* 'vehicle'. -/
def che : Noun :=
  { form := "chē", hanzi := "车", gloss := "vehicle", counters := {some Classifiers.liang} }

/-- 灯 *dēng* 'lamp'. -/
def deng : Noun :=
  { form := "dēng", hanzi := "灯", gloss := "lamp", counters := {some Classifiers.zhan} }

/-- 马 *mǎ* 'horse'. -/
def ma : Noun := { form := "mǎ", hanzi := "马", gloss := "horse", counters := {some Classifiers.pi} }

/-- 牛 *niú* 'cattle, cow', with *tóu* and *tiáo*. -/
def niu : Noun :=
  { form := "niú", hanzi := "牛", gloss := "cattle",
    counters := {some Classifiers.tou, some Classifiers.tiao} }

/-- 书 *shū* 'book', with *běn* for the thing and *bù* for the work. -/
def shu : Noun :=
  { form := "shū", hanzi := "书", gloss := "book",
    counters := {some Classifiers.ben, some Classifiers.bu} }

/-- 床 *chuáng* 'bed'. -/
def chuang : Noun :=
  { form := "chuáng", hanzi := "床", gloss := "bed", counters := {some Classifiers.zhang} }

/-- 桌子 *zhuōzi* 'table'. -/
def zhuozi : Noun :=
  { form := "zhuōzi", hanzi := "桌子", gloss := "table", counters := {some Classifiers.zhang} }

/-- 刀 *dāo* 'knife'. -/
def dao : Noun :=
  { form := "dāo", hanzi := "刀", gloss := "knife", counters := {some Classifiers.ba} }

/-- 毛笔 *máobǐ* 'brush-pen', elongated but counted with *zhī* 枝 rather than *tiáo*. -/
def maobi : Noun :=
  { form := "máobǐ", hanzi := "毛笔", gloss := "brush-pen", counters := {some Classifiers.zhiBranch} }

/-- 箭 *jiàn* 'arrow', elongated but counted with *zhī* 枝 rather than *tiáo*. -/
def jian : Noun :=
  { form := "jiàn", hanzi := "箭", gloss := "arrow", counters := {some Classifiers.zhiBranch} }

/-- 蛇 *shé* 'snake'. -/
def she : Noun :=
  { form := "shé", hanzi := "蛇", gloss := "snake", counters := {some Classifiers.tiao} }

/-- 鱼 *yú* 'fish'. -/
def yu : Noun :=
  { form := "yú", hanzi := "鱼", gloss := "fish", counters := {some Classifiers.tiao} }

/-- 绳子 *shéngzi* 'rope'. -/
def shengzi : Noun :=
  { form := "shéngzi", hanzi := "绳子", gloss := "rope", counters := {some Classifiers.tiao} }

/-- 路 *lù* 'road'. -/
def lu : Noun :=
  { form := "lù", hanzi := "路", gloss := "road", counters := {some Classifiers.tiao} }

/-- 河 *hé* 'river', with *tiáo* and *dào*. -/
def he : Noun :=
  { form := "hé", hanzi := "河", gloss := "river",
    counters := {some Classifiers.tiao, some Classifiers.dao} }

/-- 新闻 *xīnwén* 'news', counted with *tiáo* though not elongated. -/
def xinwen : Noun :=
  { form := "xīnwén", hanzi := "新闻", gloss := "news", counters := {some Classifiers.tiao} }

/-- 法律 *fǎlǜ* 'law', counted with *tiáo* though not elongated. -/
def falu : Noun :=
  { form := "fǎlǜ", hanzi := "法律", gloss := "law", counters := {some Classifiers.tiao} }

/-- 菜 *cài* 'course of food', counted with *dào*. -/
def cai : Noun :=
  { form := "cài", hanzi := "菜", gloss := "course of food", counters := {some Classifiers.dao} }

/-- 大炮 *dàpào* 'artillery piece'. -/
def dapao : Noun :=
  { form := "dàpào", hanzi := "大炮", gloss := "artillery piece", counters := {some Classifiers.men} }

/-! ### Nouns with no classifier -/

/-- 天 *tiān* 'day' denotes a measure and is counted without a classifier, *sān tiān* 'three
days', not *sān ge tiān*. -/
def tian : Noun := { form := "tiān", hanzi := "天", gloss := "day", counters := {none} }

/-- 酒 *jiǔ* 'wine' is counted through a measure word, *bēi jiǔ* 'glasses of wine'. -/
def jiu : Noun := { form := "jiǔ", hanzi := "酒", gloss := "wine", counters := ∅ }

/-- 饭 *fàn* 'cooked rice' is counted through a measure word, *yī guō fàn* 'a pot of rice'. -/
def fan : Noun := { form := "fàn", hanzi := "饭", gloss := "cooked rice", counters := ∅ }

/-- The nouns. -/
def nouns : List Noun :=
  [ren, wenti, xiansheng, gou, shou, yifu, hua, cao, feiji, che, deng, ma, niu, shu, chuang,
    zhuozi, dao, maobi, jian, she, yu, shengzi, lu, he, xinwen, falu, cai, dapao, tian, jiu, fan]

theorem not_takes_tian (c : Classifier) : ¬ tian.Takes c := Noun.not_takes_of_eq_empty rfl c

/-! ### Proper names -/

/-- A Mandarin name is the root name with the pinyin as citation form, and its characters. -/
structure ProperName extends _root_.ProperName where
  /-- The characters. -/
  hanzi : String
  deriving DecidableEq, Repr

/-- A personal name glossed by its pinyin. -/
def name (form hanzi : String) : ProperName := { form, gloss := form, hanzi }

def zhangsan : ProperName := name "Zhāngsān" "张三"
def lisi : ProperName := name "Lǐsì" "李四"
def xiaoming : ProperName := name "Xiǎomíng" "小明"

end Mandarin.Nouns
