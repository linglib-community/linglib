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
  attitude := some (.doxastic .veridical)
  factivity := some .semi

/-- *neki* 'think', whose complement does not project ((35), (36), (48)). -/
def neki : Verb where
  morphs := [.root "neki"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .nonVeridical)

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
  attitude := some (.doxastic .veridical)
  factivity := some .semi

/-- The predicates with per-predicate data in the paper. -/
def verbs : List Verb :=
  [liloy, etqew, cicwaay, eeys, qeese, timneneki, timiipni, neki, hi, cuukwe]

/-! ### Relative-pronoun paradigm

The *yox̂/ko* paradigm from [deal-2016a], reproduced at [deal-2026] (22).
Cells are indexed by `NezPerce.Case` × `Number`. -/

/-- A relative-pronoun cell from [deal-2026] (22). -/
structure RelativePronoun where
  case : Case
  number : Number
  forms : List String  -- multiple if idiolectal variation
  deriving Repr

def rp_nom_sg : RelativePronoun := ⟨.nom, .singular, ["yox̂"]⟩
def rp_nom_pl : RelativePronoun := ⟨.nom, .plural, ["yox̂me"]⟩
def rp_erg_sg : RelativePronoun := ⟨.erg, .singular, ["konim"]⟩
def rp_erg_pl : RelativePronoun := ⟨.erg, .plural, ["konmam"]⟩
def rp_acc_sg : RelativePronoun := ⟨.acc, .singular, ["konya"]⟩
def rp_acc_pl : RelativePronoun := ⟨.acc, .plural, ["konmana", "yox̂mene"]⟩

/-- The full paradigm has three cases × two numbers, six cells. -/
def relativePronounParadigm : List RelativePronoun :=
  [rp_nom_sg, rp_nom_pl, rp_erg_sg, rp_erg_pl, rp_acc_sg, rp_acc_pl]

end NezPerce
