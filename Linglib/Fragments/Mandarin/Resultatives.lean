module

public import Linglib.Fragments.Mandarin.Verbs
public import Linglib.Morphology.Word.Tree

/-!
# Mandarin resultative compounds

A Mandarin V-V resultative compound pairs a verb describing the causing event with a verb
describing its result: *dǎ-pò* 打破 'hit-break', *kū-lèi* 哭累 'cry-tired'. This file enters
the component verbs and the compounds built from them, so a compound's argument structure is
read off its verbs rather than stipulated: the result verb of every entry is monovalent, a
change-of-state verb such as *pò* 'break' or a stative such as *lèi* 'tired'
(`valency_v2`). Which argument the result is predicated of is not a property of the entry:
*zhuī-lèi* 'chase-tired' with an object is read with either the chaser or the chased tired,
so orientation belongs to a sentence, and the studies state it about the sentences they
analyze. Tay's account of the compounds as words built in morphology lives in
`Studies/Tay2024.lean`.

## Main definitions

* `Mandarin.Resultative` — a V-V resultative compound, its causing verb and its result verb.
* `Mandarin.Resultative.tree` — the compound as a root compound of its verbs.
* `Mandarin.resultatives` — the inventory of the entries.

## References

* [tay-2024]
-/

@[expose] public section

namespace Mandarin

open ArgumentStructure

/-! ### Component verbs -/

/-- 打 *dǎ* 'hit'. -/
def da : Verb :=
  { morphs := [.root "dǎ"], script := some "打", valency := .ofFrame ArgumentFrame.np,
    vendlerClass := some .activity }

/-- 哭 *kū* 'cry'. -/
def ku : Verb :=
  { morphs := [.root "kū"], script := some "哭", valency := .ofFrame ArgumentFrame.intransitive,
    vendlerClass := some .activity }

/-- 吃 *chī* 'eat'. -/
def chi : Verb :=
  { morphs := [.root "chī"], script := some "吃",
    valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [0])],
    vendlerClass := some .activity }

/-- 喝 *hē* 'drink'. -/
def he : Verb :=
  { morphs := [.root "hē"], script := some "喝",
    valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [0])],
    vendlerClass := some .activity }

/-- 推 *tuī* 'push'. -/
def tui : Verb :=
  { morphs := [.root "tuī"], script := some "推", valency := .ofFrame ArgumentFrame.np,
    vendlerClass := some .activity }

/-- 追 *zhuī* 'chase'. -/
def zhui : Verb :=
  { morphs := [.root "zhuī"], script := some "追", valency := .ofFrame ArgumentFrame.np,
    vendlerClass := some .activity }

/-- 射 *shè* 'shoot'. -/
def she : Verb :=
  { morphs := [.root "shè"], script := some "射", valency := .ofFrame ArgumentFrame.np,
    vendlerClass := some .activity }

/-- 破 *pò* 'break', intransitive. -/
def po : Verb :=
  { morphs := [.root "pò"], script := some "破", valency := .ofFrame ArgumentFrame.intransitive,
    vendlerClass := some .achievement }

/-- 死 *sǐ* 'die'. -/
def si : Verb :=
  { morphs := [.root "sǐ"], script := some "死", valency := .ofFrame ArgumentFrame.intransitive,
    vendlerClass := some .achievement }

/-- 开 *kāi* 'open', intransitive. -/
def kai : Verb :=
  { morphs := [.root "kāi"], script := some "开", valency := .ofFrame ArgumentFrame.intransitive,
    vendlerClass := some .achievement }

/-- 累 *lèi* 'tired'. -/
def lei : Verb :=
  { morphs := [.root "lèi"], script := some "累", valency := .ofFrame ArgumentFrame.intransitive,
    vendlerClass := some .state }

/-- 饱 *bǎo* 'full'. -/
def bao : Verb :=
  { morphs := [.root "bǎo"], script := some "饱", valency := .ofFrame ArgumentFrame.intransitive,
    vendlerClass := some .state }

/-- 湿 *shī* 'wet'. -/
def shi : Verb :=
  { morphs := [.root "shī"], script := some "湿", valency := .ofFrame ArgumentFrame.intransitive,
    vendlerClass := some .state }

/-- 醉 *zuì* 'drunk'. -/
def zui : Verb :=
  { morphs := [.root "zuì"], script := some "醉", valency := .ofFrame ArgumentFrame.intransitive,
    vendlerClass := some .state }

/-! ### Compounds -/

/-- A V-V resultative compound pairs a verb describing the causing event with a verb describing
its result. -/
structure Resultative where
  /-- The first verb, describing the causing event. -/
  v1 : Verb
  /-- The second verb, describing the result. -/
  v2 : Verb
  deriving BEq

/-- *dǎ-pò* 打破 'hit-break', 'break by hitting', Tay's (668). -/
def da_po : Resultative := ⟨da, po⟩

/-- *shè-sǐ* 射死 'shoot-die', 'shoot dead', Tay's (107). -/
def she_si : Resultative := ⟨she, si⟩

/-- *tuī-kāi* 推开 'push-open', Tay's (60). -/
def tui_kai : Resultative := ⟨tui, kai⟩

/-- *kū-lèi* 哭累 'cry-tired', 'cry oneself tired', Tay's (219). -/
def ku_lei : Resultative := ⟨ku, lei⟩

/-- *kū-shī* 哭湿 'cry-wet', 'become wet from crying', Tay's (221). -/
def ku_shi : Resultative := ⟨ku, shi⟩

/-- *zhuī-lèi* 追累 'chase-tired', read with either the chaser or the chased tired, Tay's (362)
after Li. -/
def zhui_lei : Resultative := ⟨zhui, lei⟩

/-- *chī-bǎo* 吃饱 'eat-full', 'become full from eating', Tay's (3). -/
def chi_bao : Resultative := ⟨chi, bao⟩

/-- *hē-zuì* 喝醉 'drink-drunk', 'drink oneself drunk', Tay's (360). -/
def he_zui : Resultative := ⟨he, zui⟩

/-- The inventory of the compounds. -/
def resultatives : List Resultative :=
  [da_po, she_si, tui_kai, ku_lei, ku_shi, zhui_lei, chi_bao, he_zui]

namespace Resultative

/-- The compound as a root compound of its two verbs. -/
def tree (c : Resultative) : Morphology.Word.Tree Verb := .compound (.root c.v1) (.root c.v2)

@[simp] theorem toList_tree (c : Resultative) : c.tree.toList = [c.v1, c.v2] := rfl

theorem valency_v2 : ∀ c ∈ resultatives, ∀ fr ∈ c.v2.valency.frames, fr.valency = 1 := by decide

end Resultative

end Mandarin
