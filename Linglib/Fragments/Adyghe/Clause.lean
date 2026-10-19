module

public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Adyghe clausal embedding

Adyghe (Northwest Caucasian, ISO 639-3 `ady`) has no embedded declarative and no embedded
polar interrogative of the matrix shape. A tensed clause under *gʷəpšəsa* 'think', *ŝe* 'know',
*gʷərəʔʷe* 'understand', *ʔʷa* 'say' or *qəč'ewəpč'a* 'ask' has the shape of a relative
clause: its verb carries the relativizer *ze-* and the applicative *re-*, and the clause ends in
the case suffix a noun phrase would bear, absolutive *-r* or oblique *-m* according to the
matrix predicate. A constituent question under 'ask' is a headless relative without *re-*, and
the same predicates take plain noun-phrase objects. The volitional and aspectual predicates such
as *raʔežʼa* 'begin' take an infinitive in *-new* instead.

Forms follow Caponigro and Polinsky's transliteration: ʷ marks labialization, ʼ ejectives, ə
schwa. Factivity values are textbook consensus for the predicate concepts; the paper runs no
projection tests. The data are Caponigro and Polinsky's; the relativization analysis is stated
in `Studies/Deal2026.lean`.

## References

* [caponigro-polinsky-2011]
-/

@[expose] public section

namespace Adyghe

/-! ### Clause-typers -/

/-- The relativizer *ze-* with the applicative *re-*, on the verb of every tensed clause under an
attitude predicate; the clause ends in a case suffix ((98), (99), (108)). -/
def zeRe : Complementizer where
  morphs := [.pref "ze", .pref "re"]
  coding := some .indicative
  licenser := some .nominal

/-- The infinitive suffix *-new* of the volitional and aspectual class ((54)). -/
def new : Complementizer where
  morphs := [.suff "new"]
  coding := some .infinitive
  licenser := some .verbal

/-! ### Predicates -/

/-- The case suffix at the right edge of a predicate's clausal complement, absolutive *-r* or
oblique *-m*, which the matrix predicate assigns ((98), (99)). -/
inductive ComplementCase where
  | abs
  | obl
  deriving DecidableEq, Repr

/-- An Adyghe complement-taking predicate is a verb entry with the case it assigns to a clausal
complement. -/
structure Verb extends _root_.Verb where
  /-- The case suffix on the clausal complement, `none` for an infinitival complement. -/
  complementCase : Option ComplementCase

/-- *gʷəpšəsa* 'think', which rejects a bare finite complement, takes the relative-shaped one,
and takes plain noun-phrase objects ((96), (98), (102)). -/
def gwepshesa : Verb where
  morphs := [.root "gʷəpšəsa"]
  valency := .of [(ArgumentFrame.finiteClause, [0, 1]), (ArgumentFrame.np, [0, 1])]
  attitude := some (.doxastic .nonVeridical)
  complementCase := some .abs

/-- *qəč'ewəpč'a* 'ask', whose polar-question complement carries *ze-re-* and whose
constituent-question complement is a headless relative; it takes plain noun-phrase objects
((69), (99), (103)). -/
def chewepcha : Verb where
  morphs := [.root "qəč'ewəpč'a"]
  valency := .of [(ArgumentFrame.question, [0, 1]), (ArgumentFrame.np, [0, 1])]
  speechActVerb := true
  complementCase := some .obl

/-- *ŝe* 'know', also *jeŝe*, whose one relative-shaped complement is ambiguous between the
declarative and the polar reading ((101)). -/
def she : Verb where
  morphs := [.root "ŝe"]
  valency := .of [(ArgumentFrame.finiteClause, [0, 1]), (ArgumentFrame.question, [0, 1])]
  attitude := some (.doxastic .veridical)
  factivity := some .semi
  complementCase := some .abs

/-- *gʷərəʔʷe* 'understand', whose complement is truth-conditionally equivalent with and
without an overt head noun 'news' or 'verity' ((108)–(110)). -/
def gwereqwe : Verb where
  morphs := [.root "gʷərəʔʷe"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .veridical)
  factivity := some .semi
  complementCase := some .abs

/-- *ʔʷa* 'say'. -/
def qwa : Verb where
  morphs := [.root "ʔʷa"]
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  complementCase := some .abs

/-- *raʔežʼa* 'begin', which takes an infinitive in *-new* ((54)). -/
def raqezha : Verb where
  morphs := [.root "raʔežʼa"]
  valency := .ofFrame ArgumentFrame.infinitival
  complementCase := none

/-- The predicates with per-predicate data in the paper. -/
def verbs : List Verb := [gwepshesa, chewepcha, she, gwereqwe, qwa, raqezha]

end Adyghe
