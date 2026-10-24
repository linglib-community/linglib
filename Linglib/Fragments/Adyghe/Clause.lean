module

public import Linglib.Fragments.Adyghe.Case
public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Syntax.Category.Verb.ArgumentFrame.Takes

/-!
# Adyghe clausal embedding

Adyghe (Northwest Caucasian, ISO 639-3 `ady`) embeds no clause of the matrix shape. Under
*gʷəpšəsa* 'think', *ṣ̂e* 'know', *gʷərəʔʷe* 'understand', *ʔʷa* 'say' or *qəč̣'ewəpč̣a* 'ask', a
tensed declarative or polar complement is a relative clause whose verb carries the relativizer
*ze-* and the high applicative *re-*, and it ends in the case suffix the matrix predicate assigns
a noun phrase, the absolutive *-r* or the oblique *-m*. The same clause conveys a declarative
under 'think', a polar question under 'ask', and either under 'know'. A constituent question
under 'ask' is a headless relative without *re-*. The one other kind of embedded clause is an
infinitival or converbal TP, as the infinitive in *-new* under the aspectual raising predicate
*raʁež'a* 'begin'.

The data are Caponigro and Polinsky's. The factivity values are the textbook ones of the
predicate concepts; the relative clauses carry no presupposition of their own.

## Main results

* `Adyghe.typers_eq`: a predicate takes *ze-re-* when its complement bears case, the
  infinitive otherwise, and no other clause-typer.

## Implementation notes

`Complementizer` is the substrate's clause-typing morpheme, not a C head: Caponigro and Polinsky
argue that *ze-re-* is no complementizer, and the entry's morphs are the relativizer and the
high applicative. Deal's relativization analysis is in `Studies/Deal2026.lean`.

## Errata

* (109)–(111) spell the matrix verb *ə-gʷəreʁ*, (108) *ə-gʷərəʔʷeʁ*, all glossed
  '3SG.ERG-understood'; the entry follows (108).
* The text before (73) says the plain noun phrase under 'ask' bears the oblique *-m*, but
  *sə-c̣e* 'my name' in (73) and (103) has no case suffix.

## References

* [caponigro-polinsky-2011]
-/

@[expose] public section

namespace Adyghe

open Morphology (Morph)

/-! ### Clause-typers -/

/-- The relativizer *zV-*, in the agreement slot of a relativized argument other than the
absolutive, its vowel *ə*, *e* or none by the phonological environment ((35), (39)). -/
def relativizer : Morph := .pref "ze"

/-- The high applicative *re-*, above every other applicative and only in relative clauses
((107)). -/
def highApplicative : Morph := .pref "re"

/-- The relativizer with the high applicative, on the verb of a relative clause conveying a
declarative or a polar question ((98), (99), (101)). -/
def zeRe : Complementizer where
  morphs := [relativizer, highApplicative]
  coding := some .indicative
  types := .of {.declarative, .polar}
  licenser := some .nominal

/-- The infinitive suffix *-new* ((54)). -/
def new : Complementizer where
  morphs := [.suff "new"]
  coding := some .infinitive
  licenser := some .verbal

/-- The clause-typers. -/
def complementizers : List Complementizer := [zeRe, new]

/-! ### Predicates -/

/-- An Adyghe complement-taking predicate is a verb entry with the case it assigns its nominal
complement, a noun phrase or a relative clause alike. -/
structure Verb extends _root_.Verb where
  /-- The case of the nominal complement, `none` for a predicate without one. -/
  complementCase : Option Case := none

/-- *gʷəpšəsa* 'think', with a relative clause or a noun phrase in the absolutive ((96), (98),
(102)). -/
def gwepshesa : Verb where
  morphs := [.root "gʷəpšəsa"]
  valency := .ofFrames [ArgumentFrame.finiteClause, ArgumentFrame.np]
  attitude := some (.doxastic .nonVeridical)
  complementCase := some .abs

/-- *qəč̣'ewəpč̣a* 'ask', with a relative clause conveying a question or a noun phrase, in the
oblique ((69), (99), (103), (116)). -/
def chewepcha : Verb where
  morphs := [.root "qəč̣'ewəpč̣a"]
  valency := .ofFrames [ArgumentFrame.question, ArgumentFrame.np]
  speechActVerb := true
  complementCase := some .obl

/-- *ṣ̂e* 'know', also *jeṣ̂e*, with a relative clause conveying a declarative or a polar question
or a noun phrase, in the absolutive ((75), (101), (104)). -/
def she : Verb where
  morphs := [.root "ṣ̂e"]
  valency := .ofFrames [ArgumentFrame.finiteClause, ArgumentFrame.question, ArgumentFrame.np]
  attitude := some (.doxastic .veridical)
  factivity := some .semi
  complementCase := some .abs

/-- *gʷərəʔʷe* 'understand', whose complement means the same with and without an overt head
*qeba* 'news' or *ṣ̂əpqə* 'verity' ((108)–(110)). -/
def gwereqwe : Verb where
  morphs := [.root "gʷərəʔʷe"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .veridical)
  factivity := some .semi
  complementCase := some .abs

/-- *ʔʷa* 'say' (fn. 12). -/
def qwa : Verb where
  morphs := [.root "ʔʷa"]
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  complementCase := some .abs

/-- *raʁež'a* 'begin', a raising predicate over an infinitive ((54)). -/
def raghezha : Verb where
  morphs := [.root "raʁež'a"]
  valency := .ofFrame ArgumentFrame.raising

/-- The predicates with per-predicate data in the paper. -/
def verbs : List Verb := [gwepshesa, chewepcha, she, gwereqwe, qwa, raghezha]

theorem typers_eq :
    ∀ v ∈ verbs, v.typers complementizers = [if v.complementCase.isSome then zeRe else new] := by
  decide

end Adyghe
