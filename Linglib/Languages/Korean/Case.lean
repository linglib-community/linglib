module

public import Linglib.Core.Data.Fintype.Order
public import Linglib.Languages.Korean.Phonology
public import Linglib.Morphology.Exponence.SubsetRule
public import Linglib.Morphology.Morph
public import Linglib.Syntax.Feature.Case.Function

/-!
# Korean case markers

Korean marks case with postpositional particles, which Sohn treats as bound words rather than
clitics. Several have two forms chosen by the final segment of the noun: the nominative *-ga* after
a vowel and *-i* after a consonant, and likewise the accusative *-reul* and *-eul*, the
instrumental *-ro* and *-euro*, and the comitative *-wa* and *-gwa*. A particle is recorded as its
variants of register, each a set of forms with the final segments it follows, among which [the
most specific one that fits is chosen](##Korean.Case.forms). Casual speech drops the nominative,
accusative, genitive and dative particles.

## Implementation notes

* Forms are in the Revised Romanization; Sohn writes *ka*, *lul*, *uy*, *eykey*, *hanthey*, *kkey*,
  *ey*, *eyse*, *puthe*, *lo* and *wa*.
* A form's condition is a partial segment, which a final segment meets by extending it, so that
  the form with no condition is the one found elsewhere.

## References

* [sohn-1994]
* [sohn-1999]
-/

@[expose] public section

namespace Korean

/-- The case particles. -/
inductive Case where
  /-- The nominative *-ga* after a vowel and *-i* after a consonant. -/
  | ga
  /-- The accusative *-reul* after a vowel and *-eul* after a consonant. -/
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
  /-- The ablative *-buteo* 'from', also after *-eseo* and the instrumental. -/
  | buteo
  /-- The instrumental and the directional 'toward', *-ro* after a vowel or *l* and *-euro* after
  another consonant. -/
  | ro
  /-- The comitative, formal *-wa* after a vowel and *-gwa* after a consonant, and informal *-hago*
  and *-rang* after a vowel, *-irang* after a consonant. -/
  | wa
  deriving DecidableEq, Fintype, Repr

namespace Case

open Phonology Morphology

/-- The forms of a particle after a vowel and after a consonant, the slashed pairs of Sohn's table
of case particles ([sohn-1999], pp. 213–214). -/
def alternating (afterVowel afterConsonant : String) : RuleSet (SubsetRule Segment Morph) :=
  [⟨[+syllabic], .encl afterVowel⟩, ⟨⊥, .encl afterConsonant⟩]

/-- A particle with one form. -/
def invariant (form : String) : RuleSet (SubsetRule Segment Morph) := [⟨⊥, .encl form⟩]

/-- The variants of a particle, each the forms it has with the final segments of the noun they
follow. The vowel of *-euro* is also lost after *l*, which behaves like a vowel there
([sohn-1999], p. 190). -/
def variants : Case → List (RuleSet (SubsetRule Segment Morph))
  | ga => [alternating "ga" "i"]
  | reul => [alternating "reul" "eul"]
  | ui => [invariant "ui"]
  | ege => [invariant "ege", invariant "hante"]
  | kke => [invariant "kke"]
  | e => [invariant "e"]
  | eseo => [invariant "eseo"]
  | buteo => [invariant "buteo"]
  | ro => [⟨l, .encl "ro"⟩ :: alternating "ro" "euro"]
  | wa => [alternating "wa" "gwa", invariant "hago", alternating "rang" "irang"]

/-- The forms of a particle after a noun ending in the segment `s`, one for each variant: of the
forms whose condition `s` meets, the one with the most specific condition. -/
def forms (c : Case) (s : Segment) : List Morph :=
  c.variants.filterMap (·.realizeMinimal (fun r ↦ OrderDual.toDual r.features) s)

/-- The forms of a particle, its allomorphs and variants. -/
def exponents (c : Case) : List Morph := (c.variants.flatMap (·.map (·.exponent))).dedup

/-- The nominative is *-ga* after a vowel and *-i* after a consonant, *l* included. -/
theorem forms_ga :
    ga.forms a = [.encl "ga"] ∧ ga.forms k = [.encl "i"] ∧ ga.forms l = [.encl "i"] := by
  decide

/-- The instrumental is *-ro* after a vowel and after *l*, and *-euro* after other consonants, a
nasal among them. -/
theorem forms_ro :
    ro.forms a = [.encl "ro"] ∧ ro.forms l = [.encl "ro"] ∧ ro.forms n = [.encl "euro"] ∧
      ro.forms k = [.encl "euro"] := by
  decide

theorem forms_wa :
    wa.forms a = [.encl "wa", .encl "hago", .encl "rang"] ∧
      wa.forms k = [.encl "gwa", .encl "hago", .encl "irang"] := by
  decide

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

/-- The functions a particle marks: *-e* also the goal, *-eseo* also the source, and
*-(eu)ro* also the direction of motion. -/
def functions : Case → Finset _root_.Case.Function
  | e => {.spatial none .place, .spatial none .goal}
  | eseo => {.spatial none .place, .spatial none .source}
  | ro => {.instrumental, .spatial none .goal}
  | buteo => {.spatial none .source}
  | c => c.label.functions

theorem label_functions_inter_nonempty (c : Case) :
    (c.label.functions ∩ c.functions).Nonempty := by
  cases c <;> decide

end Case

end Korean
