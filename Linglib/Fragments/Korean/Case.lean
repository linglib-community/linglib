module

public import Linglib.Morphology.Morph
public import Linglib.Syntax.Case.Basic

/-!
# Korean case markers

Korean marks case with postpositional particles, which Sohn treats as bound words rather than
clitics, several with allomorphs chosen by the final segment of the noun: the nominative *-i* after
a consonant and *-ga* after a vowel, the accusative *-eul* and *-reul*, the genitive *-ui*, the
dative *-ege*, colloquially *-hante* and to a social superior *-kke*, the locative *-e* of a state
and goal and *-eseo* of an action and source, the ablative *-buteo*, the instrumental and
directional *-(eu)ro*, and the comitative, formal *-gwa* and *-wa* and informal *-hago* and
*-(i)rang* ([sohn-1999], p. 339). Casual speech drops the nominative, accusative, genitive and
dative particles. Forms are in the Revised Romanization; Sohn writes *ka*, *(l)ul*, *uy*, *eykey*,
*hanthey*, *kkey*, *ey*, *eyse*, *pwuthe*, *(u)lo* and *(k)wa*.

## Main definitions

* `Korean.Case`, `Korean.Case.exponents`: the case particles, with their allomorphs.
* `Korean.Case.label`, `Korean.Case.functions`: the comparative value each is named for, and the
  values it expresses.

## References

* [sohn-1994]
* [sohn-1999]
-/

@[expose] public section

namespace Korean

/-- The case particles. -/
inductive Case where
  /-- The nominative *-i* after a consonant and *-ga* after a vowel. -/
  | ga
  /-- The accusative *-eul* after a consonant and *-reul* after a vowel. -/
  | reul
  /-- The genitive *-ui*. -/
  | ui
  /-- The dative *-ege*, colloquially *-hante*. -/
  | ege
  /-- The honorific dative *-kke*. -/
  | kke
  /-- *-e*, the locative of a state and the goal of motion. -/
  | e
  /-- *-eseo*, the locative of an action and the source of motion. -/
  | eseo
  /-- The ablative *-buteo* 'from', also after *-eseo* and *-(eu)ro*. -/
  | buteo
  /-- *-(eu)ro*, the instrumental and the directional 'toward'. -/
  | ro
  /-- The comitative *-gwa* after a consonant and *-wa* after a vowel, *-hago*, and the casual
  *-(i)rang*. -/
  | wa
  deriving DecidableEq, Fintype, Repr

namespace Case

/-- The forms of a particle, its allomorphs and variants, with a segment in parentheses where one
allomorph lacks it. -/
def exponents : Case → List Morphology.Morph
  | ga => [.encl "i", .encl "ga"]
  | reul => [.encl "eul", .encl "reul"]
  | ui => [.encl "ui"]
  | ege => [.encl "ege", .encl "hante"]
  | kke => [.encl "kke"]
  | e => [.encl "e"]
  | eseo => [.encl "eseo"]
  | buteo => [.encl "buteo"]
  | ro => [.encl "(eu)ro"]
  | wa => [.encl "(g)wa", .encl "hago", .encl "(i)rang"]

/-- The comparative value a particle is named for. -/
def label : Case → _root_.Case
  | ga => .nom
  | reul => .acc
  | ui => .gen
  | ege | kke => .dat
  | e | eseo => .loc
  | buteo => .abl
  | ro => .inst
  | wa => .com

/-- The comparative values a particle expresses: *-e* also the goal, *-eseo* also the source, and
*-(eu)ro* also the direction of motion. -/
def functions : Case → Finset _root_.Case
  | e => {.loc, .all}
  | eseo => {.loc, .abl}
  | ro => {.inst, .all}
  | c => {c.label}

theorem label_mem_functions (c : Case) : c.label ∈ c.functions := by
  cases c <;> decide

end Case

end Korean
