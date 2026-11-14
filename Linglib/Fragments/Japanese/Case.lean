module

public import Linglib.Morphology.Morph
public import Linglib.Syntax.Case.Basic

/-!
# Japanese case markers

Japanese marks the relations of a noun phrase with particles after it. Tsujimura separates the
case particles, the nominative *ga*, the accusative *o*, the dative *ni* and the genitive *no*,
from the postpositions, the counterparts of English prepositions (`Japanese.Adpositions`): *de*
'at', *e* 'to', *to* 'with', *made* 'until' and *kara* 'from'. The nominative and the
accusative, unlike case endings, may be dropped in casual speech, *Tomodati(-ga) kita?* 'Has my
friend come?', and replaced by *mo* 'also' and *sae* 'even'. Two markers are polysemous: *ni*
marks recipients, goals, times and the location of existence, and *de* the location of an
action and its instrument, so *ni* and *de* share the locative and *ni* and *e* the allative.
*Ga* is recorded as the nominative, setting aside the exhaustive-listing reading of Kuroda and
Kuno; *no* is also a nominalizer, *to* a quotative complementizer and *kara* a reason
conjunction, uses outside case marking. Sadakane and Koizumi's four *ni* lexemes refine the
single *ni* entry, the matter of `Studies/SadakaneKoizumi1995.lean`.

## Main definitions

* `Japanese.Case`, `Japanese.Case.exponents`: the four cases of the case particles, and the
  particles.
* `Japanese.Case.label`, `Japanese.Case.functions`: the comparative value each case is named for,
  and the values it expresses.
* `Japanese.Case.droppable`: the cases whose particles casual speech drops.

## References

* [kuno-1973]
* [kuroda-1965]
* [sadakane-koizumi-1995]
* [tsujimura-2014]
-/

@[expose] public section

namespace Japanese

/-! ### Case particles -/

/-- The four cases the case particles mark. -/
inductive Case where
  /-- The nominative, *ga*. -/
  | nom
  /-- The accusative, *o*. -/
  | acc
  /-- The genitive, *no*. -/
  | gen
  /-- The dative, *ni*. -/
  | dat
  deriving DecidableEq, Fintype, Repr

namespace Case

/-- `c.exponents` is the case particle of `c`, enclitic *ga* が, *o* を, *no* の or *ni* に. -/
def exponents : Case → List Morphology.Morph
  | nom => [.encl "ga"]
  | acc => [.encl "o"]
  | gen => [.encl "no"]
  | dat => [.encl "ni"]

/-- The comparative value a case is named for. -/
def label : Case → _root_.Case
  | nom => .nom
  | acc => .acc
  | gen => .gen
  | dat => .dat

/-- `c.functions` are the comparative values `c` expresses; *ni* marks the recipient, the goal,
the time and the location of existence. -/
def functions : Case → Finset _root_.Case
  | dat => {.dat, .loc, .all, .tem}
  | c => {c.label}

theorem label_mem_functions (c : Case) : c.label ∈ c.functions := by
  cases c <;> decide

/-- The cases whose particles casual speech drops, the nominative and the accusative. -/
def droppable : Finset Case := {nom, acc}

end Case

end Japanese
