module

/-!
# Cantonese phase complements

The postverbal phase complements of Cantonese, the grammaticalized second verbs that mark the
completion, attainment or result of the event, following [matthews-yip-1994] and
[cheung-2007], with the adversative *-can* of [sio-2020] and the anticipatory *-ding* of
[wong-shing-kit-2018]. The continuous *-zyu* is an aspect suffix and is entered in
`Languages/Cantonese/Aspect.lean`. The classification of these complements as inner aspect, and
the diagnostics separating them from resultative verb compounds, are the analysis of
[liu-yip-2026].

## References

* [matthews-yip-1994]
* [cheung-2007]
* [sio-2020]
* [wong-shing-kit-2018]
* [liu-yip-2026]
-/

@[expose] public section

namespace Cantonese.ResultativeComplements

/-- A Cantonese phase complement: its jyutping, its character, its gloss and a representative
verb it combines with. -/
structure PhaseComplement where
  /-- The jyutping form with tone number. -/
  jyutping : String
  /-- The character. -/
  hanzi : String
  /-- The gloss. -/
  gloss : String
  /-- A representative verb–complement combination with its translation. -/
  example_ : String
  deriving Repr, DecidableEq

/-- *-dim* 掂 'all right': *gaau-dim* 'finished, settled'. -/
def dim : PhaseComplement :=
  { jyutping := "dim6", hanzi := "掂", gloss := "all right", example_ := "gaau2-dim6 'settled'" }

/-- *-dou* 倒 'arrive': *wan-dou* 'found'. -/
def dou : PhaseComplement :=
  { jyutping := "dou2", hanzi := "倒", gloss := "arrive", example_ := "wan2-dou2 'found'" }

/-- *-gin* 見 'see': *teng-gin* 'hear'. -/
def gin : PhaseComplement :=
  { jyutping := "gin3", hanzi := "見", gloss := "see", example_ := "teng1-gin3 'hear'" }

/-- *-hei* 起 'lift': *waak-hei* 'finished drawing'. -/
def hei : PhaseComplement :=
  { jyutping := "hei2", hanzi := "起", gloss := "lift",
    example_ := "waak6-hei2 'finished drawing'" }

/-- *-hou* 好 'good': *zou-hou* 'done'. -/
def hou : PhaseComplement :=
  { jyutping := "hou2", hanzi := "好", gloss := "good", example_ := "zou6-hou2 'done'" }

/-- *-jyun* 完 'finish': *sik-jyun* 'finished eating'. -/
def jyun : PhaseComplement :=
  { jyutping := "jyun4", hanzi := "完", gloss := "finish",
    example_ := "sik6-jyun4 'finished eating'" }

/-- *-seng* 成 'succeed': *joek-seng* 'succeeded in making an appointment'. -/
def seng : PhaseComplement :=
  { jyutping := "seng4", hanzi := "成", gloss := "succeed",
    example_ := "joek3-seng4 'succeeded in making an appointment'" }

/-- *-zoek* 著 'on target': *fan-zoek* 'fell asleep'. -/
def zoek : PhaseComplement :=
  { jyutping := "zoek6", hanzi := "著", gloss := "on target",
    example_ := "fan3-zoek6 'fell asleep'" }

/-- *-lok* 落 'finish, fall': *zyu-lok* 'taught way back then'. -/
def lok : PhaseComplement :=
  { jyutping := "lok6", hanzi := "落", gloss := "finish",
    example_ := "zyu2-lok6 'taught back then'" }

/-- *-ding* 定 'in advance' [wong-shing-kit-2018]: *zyu-ding* 'cooked in advance'. -/
def ding : PhaseComplement :=
  { jyutping := "ding6", hanzi := "定", gloss := "in advance",
    example_ := "zyu2-ding6 'cooked in advance'" }

/-- *-can* 親, the adversative [sio-2020]: *daa-can* 'injured by hitting'. -/
def can : PhaseComplement :=
  { jyutping := "can1", hanzi := "親", gloss := "adversative",
    example_ := "daa2-can1 'injured by hitting'" }

/-- *-sat* 實 'firm': *mong-sat* 'keep looking at'. -/
def sat : PhaseComplement :=
  { jyutping := "sat6", hanzi := "實", gloss := "firm",
    example_ := "mong6-sat6 'keep looking at'" }

/-- The phase complements. -/
def all : List PhaseComplement := [dim, dou, gin, hei, hou, jyun, seng, zoek, lok, ding, can, sat]

end Cantonese.ResultativeComplements
