module

public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Syntax.Category.Complementizer.Basic
public import Linglib.Syntax.Category.Verb.ArgumentFrame.Takes

/-!
# Ndebele clausal embedding

Northern Ndebele (Bantu S44, Zimbabwe, ISO 639-3 `nde`) introduces every finite complement
clause with *ukuthi*: the augment *u-*, the prefix all nominals carry, on the class-15
complementizer root *kuthi*, etymologically a nominalization of *thi* 'say'. It introduces
indicative and subjunctive complements alike, under *cabanga* 'think', *funa* 'want' and *zwa*
'hear', as the object of the preposition *nga* 'about' under *khuluma* 'talk', as a demoted
passive subject with the oblique *yi-* in place of the augment, and as a clausal subject
controlling class-15 agreement. The augment drops exactly where nominal augments drop, under
negation in situ; the complementizers *ukuze* and *sengathi* are lexically selected and occur
only with the subjunctive.

The data are Pietraszko's, the clausal positions the rows of `Data/Examples/Pietraszko2019.json`.
The paper runs no projection tests, and the 'the fact that' paraphrases in its translations are
an English artifact it flags itself.

## References

* [pietraszko-2019]
-/

@[expose] public section

namespace Ndebele

/-! ### Clause-typers -/

/-- The complementizer *ukuthi*, the augment over the class-15 root *kuthi*, on indicative and
subjunctive complements alike ((4), (7b), fn. 3). -/
def ukuthi : Complementizer where
  morphs := [.pref "u", .root "kuthi"]
  types := .only .declarative
  verbForm := some .Fin

/-! ### Predicates -/

/-- *cabanga* 'think', with an indicative complement ((4), (12)). -/
def cabanga : Verb where
  morphs := [.root "cabanga"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .nonVeridical)

/-- *funa* 'want', with a subjunctive complement and plain class-15 objects ((7)). -/
def funa : Verb where
  morphs := [.root "funa"]
  valency := .ofFrames
    [{ complements := [.clausal (coding := some .subjunctive) (types := .only .declarative)] },
     ArgumentFrame.np]
  attitude := some (.preferential .positive true)

/-- *zwa* 'hear', attested as a hearsay report ((18)). -/
def zwa : Verb where
  morphs := [.root "zwa"]
  valency := .ofFrame ArgumentFrame.finiteClause

/-- *khuluma nga* 'talk about', whose clause is the object of the preposition ((20b)). -/
def khulumaNga : Verb where
  morphs := [.root "khuluma", .free "nga"]
  valency := .ofFrame ArgumentFrame.pp
  speechActVerb := true

/-- The predicates with clausal-argument data in the paper. -/
def verbs : List Verb := [cabanga, funa, zwa, khulumaNga]

theorem takes_ukuthi :
    ∀ v ∈ verbs, ∀ fr ∈ v.valency.frames, fr.HasClausal → ArgumentFrame.Takes fr ukuthi := by
  decide

end Ndebele
