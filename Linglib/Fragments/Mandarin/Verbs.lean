module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# Mandarin verbs

The Mandarin clause-embedding predicates the studies of Qing and Uegaki, of Glass, of Wang and
of Liu and Yip consume: the preferential attitudes *qīdài* 'look forward to', *dānxīn* 'worry',
*xīwàng* 'hope' and *hàipà* 'fear', the doxastic *yǐwéi* 'think, wrongly' and *rènwéi*
'think', the factives *zhīdào* 'know' and *hòuhuǐ* 'regret', the inchoative *kāishǐ* 'start',
and the control and causative predicates *xiǎng* 'want', *ràng* 'let', *xiāngxìn*
'believe', *quàn* 'urge', *bī* 'force', *dǎsuàn* 'plan' and *shèfǎ* 'try'. Mandarin is
isolating, so an entry is a root `Verb` with no inflectional fields, its form the pinyin and
its script the characters.

## Main definitions

* `Mandarin.verbs`: the inventory of the entries.

## References

* [glass-2025]
* [qing-uegaki-2025]
* [wang-2025]
* [liu-yip-2026]
-/

@[expose] public section

namespace Mandarin

open ArgumentStructure

/-- 期待 *qīdài* 'look forward to' is a positive preferential attitude that takes questions. -/
def qidai : Verb := {
  morphs := [.root "qīdài"]
  script := some "期待"
  valency := .ofFrame ArgumentFrame.finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive false) }

/-- 担心 *dānxīn* 'worry' is a negative preferential attitude. -/
def danxin : Verb := {
  morphs := [.root "dānxīn"]
  script := some "担心"
  valency := .ofFrame ArgumentFrame.finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .negative false) }

/-- 希望 *xīwàng* 'hope' is a positive preferential attitude that takes no questions. -/
def xiwang : Verb := {
  morphs := [.root "xīwàng"]
  script := some "希望"
  valency := .ofFrame ArgumentFrame.finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true) }

/-- 害怕 *hàipà* 'fear' is a negative preferential attitude that takes questions. -/
def haipa : Verb := {
  morphs := [.root "hàipà"]
  script := some "害怕"
  valency := .ofFrame ArgumentFrame.finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .negative true) }

/-- 以为 *yǐwéi* 'be under the impression that' is a nonveridical doxastic attitude. -/
def yiwei : Verb := {
  morphs := [.root "yǐwéi"]
  script := some "以为"
  valency := .ofFrame ArgumentFrame.finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .nonVeridical) }

/-- 认为 *rènwéi* 'think, hold the view that' is the neutral nonveridical doxastic verb. -/
def renwei : Verb := {
  morphs := [.root "rènwéi"]
  script := some "认为"
  valency := .ofFrame ArgumentFrame.finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .nonVeridical) }

/-- 知道 *zhīdào* 'know', presupposing its complement and asserting belief in it; *rènwéi* is
its non-factive counterpart. -/
def zhidao : Verb := {
  morphs := [.root "zhīdào"]
  script := some "知道"
  valency := .of [(ArgumentFrame.finiteClause, [0, 1]), (ArgumentFrame.question, [0, 1])]
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .veridical)
  factivity := some .semi }

/-- 后悔 *hòuhuǐ* 'regret', the emotive factive. -/
def houhui : Verb := {
  morphs := [.root "hòuhuǐ"]
  script := some "后悔"
  valency := .ofFrame ArgumentFrame.finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .negative true)
  factivity := some .full }

/-- 开始 *kāishǐ* 'start', presupposing that the action or state was not under way before. -/
def kaishi : Verb := {
  morphs := [.root "kāishǐ"]
  script := some "开始"
  valency := .ofFrame ArgumentFrame.infinitival
  passivizable := false
  phasal := some .inception }

/-! ### Control and causative predicates

The entries record the surface form, whether the complement is finite, and who controls its
subject, the matrix subject for *xiǎng*, *dǎsuàn* and *shèfǎ* and the causee object for *ràng*,
*quàn* and *bī*, as Liu and Yip's examples show. The sizes and the dynamicity of the complements
each predicate selects are the analysis of Liu and Yip and live in `Studies/LiuYip2026.lean`. -/

/-- 想 *xiǎng* 'want' is a desiderative verb with a nonfinite complement. -/
def xiang : Verb := {
  morphs := [.root "xiǎng"]
  script := some "想"
  valency := .ofFrame ArgumentFrame.infinitival (controller := some 0)
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true) }

/-- 让 *ràng* 'let' is a manipulative verb with a nonfinite complement. -/
def rang : Verb := {
  morphs := [.root "ràng"]
  script := some "让"
  valency := .ofFrame ArgumentFrame.infinitival.withObject (controller := some 1)
  passivizable := false
  opaqueContext := false }

/-- 相信 *xiāngxìn* 'believe' is a nonveridical doxastic attitude with a finite complement. -/
def xiangxin : Verb := {
  morphs := [.root "xiāngxìn"]
  script := some "相信"
  valency := .ofFrame ArgumentFrame.finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .nonVeridical) }

/-- 劝 *quàn* 'urge' is a manipulative verb with a nonfinite complement. -/
def quan : Verb := {
  morphs := [.root "quàn"]
  script := some "劝"
  valency := .ofFrame ArgumentFrame.infinitival.withObject (controller := some 1)
  passivizable := true
  opaqueContext := false }

/-- 逼 *bī* 'force' is a manipulative verb with a nonfinite complement. -/
def bi : Verb := {
  morphs := [.root "bī"]
  script := some "逼"
  valency := .ofFrame ArgumentFrame.infinitival.withObject (controller := some 1)
  passivizable := true
  opaqueContext := false }

/-- 打算 *dǎsuàn* 'plan' is a desiderative verb with a nonfinite complement. -/
def dasuan : Verb := {
  morphs := [.root "dǎsuàn"]
  script := some "打算"
  valency := .ofFrame ArgumentFrame.infinitival (controller := some 0)
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true) }

/-- 设法 *shèfǎ* 'try' is an achievement verb with a nonfinite complement. -/
def shefa : Verb := {
  morphs := [.root "shèfǎ"]
  script := some "设法"
  valency := .ofFrame ArgumentFrame.infinitival (controller := some 0)
  passivizable := false
  opaqueContext := false }

/-- The verb inventory. -/
def verbs : List Verb :=
  [qidai, danxin, xiwang, haipa, yiwei, renwei, zhidao, houhui, kaishi,
   xiang, rang, xiangxin, quan, bi, dasuan, shefa]

end Mandarin
