module

public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Syntax.Category.Complementizer.Basic
public import Linglib.Syntax.Number.Basic
public import Linglib.Fragments.NezPerce.Case

/-!
# Nez Perce clausal embedding

Nez Perce (Sahaptian, ISO 639-3 `nez`) embeds a finite clause under an attitude predicate in
two shapes. Under the emotive predicates *lilooy* 'be happy', *’etqew* 'be sad', *cicwaay* 'be
surprised', *’eey’s* 'be joyful', *q’eese’* 'be bothered' and *tim’neeneki* 'be worried',
and under *timiipni* 'remember', the clause opens with the relative pronoun *yox̂* and the
complementizer *ke*, the edge of a relative clause, and these predicates take no noun-phrase
object. Under *neki* 'think', *hi* 'say, tell' and *cuukwe* 'know' the clause has the shape of a
matrix clause, and *hi* takes an accusative addressee. Consultants endorse the complement of the
first class and of *cuukwe* under negation, in questions and in conditional antecedents, and not
the complement of *neki*. The relative pronoun inflects for case and number.

Forms follow Deal's orthography. The data are Deal's: the judgments on each shape are the rows
of `Data/Examples/Deal2026.json`, and the relative-embedding analysis is
`Studies/Deal2026.lean`.

## References

* [deal-2026]
* [deal-2016a]
-/

@[expose] public section

namespace NezPerce

/-! ### Clause-typers -/

/-- The complementizer *ke*, which heads relative clauses and the relative embeddings. -/
def ke : Complementizer where
  morphs := [.free "ke"]
  coding := some .indicative

/-! ### Predicates -/

/-- *lilooy* 'be happy' ((27a), (28a), (33)). -/
def liloy : Verb where
  morphs := [.root "lilooy"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.preferential .positive true)
  factivity := some .full

/-- *’etqew* 'be sad' (27b). -/
def etqew : Verb where
  morphs := [.root "’etqew"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.preferential .negative true)
  factivity := some .full

/-- *cicwaay* 'be surprised' ((27c), (28b)). -/
def cicwaay : Verb where
  morphs := [.root "cicwaay"]
  valency := .ofFrame ArgumentFrame.finiteClause
  factivity := some .full

/-- *’eey’s* 'be joyful', which takes no noun-phrase object ((27e), (41)). -/
def eeys : Verb where
  morphs := [.root "’eey’s"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.preferential .positive true)
  factivity := some .full

/-- *q’eese’* 'be bothered, unhappy' (27e). -/
def qeese : Verb where
  morphs := [.root "q’eese’"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.preferential .negative true)
  factivity := some .full

/-- *tim’neeneki* 'be worried', whose complement projects under negation ((27e), (34)). -/
def timneneki : Verb where
  morphs := [.root "tim’neeneki"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.preferential .negative false)
  factivity := some .full

/-- *timiipni* 'remember', a cognitive factive with the relative edge (27d). -/
def timiipni : Verb where
  morphs := [.root "timiipni"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .epistemic)
  factivity := some .semi

/-- *neki* 'think', whose complement does not project ((35), (36), (48)). -/
def neki : Verb where
  morphs := [.root "neki"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .doxastic)

/-- *hi* 'say, tell', with an accusative addressee before the clause ((47), (65b)). -/
def hi : Verb where
  morphs := [.root "hi"]
  valency := .ofFrame
    { complements :=
        [.nominal, .clausal (coding := some .indicative) (types := .only .declarative)] }
  speechActVerb := true

/-- *cuukwe* 'know', whose complement projects from a conditional antecedent ((66), (68)). -/
def cuukwe : Verb where
  morphs := [.root "cuukwe"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .epistemic)
  factivity := some .semi

/-- The predicates with per-predicate data in the paper. -/
def verbs : List Verb :=
  [liloy, etqew, cicwaay, eeys, qeese, timneneki, timiipni, neki, hi, cuukwe]

/-! ### The relative pronoun -/

namespace RelativePronoun

/-- The number columns of the relative-pronoun table (22). -/
inductive Column where
  | sg | pl
  deriving DecidableEq, Fintype, Repr

/-- The number of a column. -/
def Column.number : Column → Number
  | .sg => .singular
  | .pl => .plural

/-- Table (22) of [deal-2026], after [deal-2016a]: the forms of the relative pronoun *yox̂* ~
*ko-* by case and number, the accusative plural in idiolectal variation. -/
def table : Case × Column → Finset String
  | (.nom, .sg) => {"yox̂"}
  | (.nom, .pl) => {"yox̂me"}
  | (.erg, .sg) => {"konim"}
  | (.erg, .pl) => {"konmam"}
  | (.acc, .sg) => {"konya"}
  | (.acc, .pl) => {"konmana", "yox̂mene"}

end RelativePronoun

end NezPerce
