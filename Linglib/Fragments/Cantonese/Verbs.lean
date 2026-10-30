module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# Cantonese complement-taking verbs

The Cantonese verbs of Liu and Yip's two lists of complement-taking predicates. The desideratives
*soeng* 'want' and *daasyun* 'intend' and the manipulatives *hyun* 'urge', *bik* 'force' and
*giu* 'ask' take a nonfinite clause; the attitude verb *seon* 'believe', the utterance verb
*gong* 'say' and the factive *geidak* 'remember' take a finite one. Each entry is a root `Verb`
whose form is the jyutping and whose script is the characters. The desideratives' subject
controls the complement's subject, and the manipulatives' object does, as in *hyun Aaming
[bou PhD]* 'urge Ming to apply for a PhD'. The size of each complement, and the scope of an
*again*-element across it, are the paper's analysis and live in `Studies/LiuYip2026.lean`.

## Main definitions

* `Cantonese.Verbs.all`: the inventory of the entries.

## References

* [liu-yip-2026]
-/

@[expose] public section

namespace Cantonese.Verbs

open ArgumentStructure

/-- 想 *soeng* 'want'. -/
def soeng : Verb where
  morphs := [.root "soeng2"]
  script := some "想"
  valency := .ofFrame ArgumentFrame.infinitival (controller := some 0)
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)

/-- 勸 *hyun* 'urge'. -/
def hyun : Verb where
  morphs := [.root "hyun3"]
  script := some "勸"
  valency := .ofFrame ArgumentFrame.infinitival.withObject (controller := some 1)

/-- 逼 *bik* 'force'. -/
def bik : Verb where
  morphs := [.root "bik1"]
  script := some "逼"
  valency := .ofFrame ArgumentFrame.infinitival.withObject (controller := some 1)

/-- 叫 *giu* 'ask, tell'. -/
def giu : Verb where
  morphs := [.root "giu3"]
  script := some "叫"
  valency := .ofFrame ArgumentFrame.infinitival.withObject (controller := some 1)

/-- 打算 *daasyun* 'intend, plan'. -/
def daasyun : Verb where
  morphs := [.root "daa2syun3"]
  script := some "打算"
  valency := .ofFrame ArgumentFrame.infinitival (controller := some 0)
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)

/-- 信 *seon* 'believe', a nonveridical doxastic attitude. -/
def seon : Verb where
  morphs := [.root "seon3"]
  script := some "信"
  valency := .ofFrame ArgumentFrame.finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .doxastic)

/-- 講 *gong* 'say'. -/
def gong : Verb where
  morphs := [.root "gong2"]
  script := some "講"
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true

/-- 記得 *geidak* 'remember', a semi-factive. -/
def geidak : Verb where
  morphs := [.root "gei3dak1"]
  script := some "記得"
  valency := .ofFrame ArgumentFrame.finiteClause
  passivizable := false
  factivity := some .semi

/-- The verbs. -/
def all : List Verb := [soeng, hyun, bik, giu, daasyun, seon, gong, geidak]

end Cantonese.Verbs
