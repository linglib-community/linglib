module

public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Washo clausal embedding

Washo (Hokan/isolate, ISO 639-3 `was`) has two ways of embedding a clause under a verb. A
verb of knowledge or perception such as *hamup'ay* 'forget' or *i:gi* 'see' takes a nominalized
clause: the clause keeps its subject agreement, tense and switch-reference marking, stays in the
independent mood *-i*, and closes with the nominalizer *-gi ~ -ge*, which inflects for case.
A verb of thought or speech such as *hamu* 'think' or *i:d* 'say' is intransitive, and the clause
it embeds is bare: it carries the dependent mood *-aʔ*, no nominalizer and no switch-reference
marking. The two classes differ in transitivity, which each verb's frames record: 'know' and 'see'
also take plain noun-phrase objects, while 'think' is questioned with *how* rather than *what*, and
'dream' embeds a bare clause only with the reflexive prefix *gum-*. 'Know', 'remember' and
'believe' are inherently negative, so their positive reading carries the negative suffix
*-e:s*, and 'remember' is negated 'forget'.

Forms follow Jacobsen's orthography: `:` marks vowel length, ʔ ɨ ŋ are IPA, and stress is
acute. The data are Bochnak and Hanink's; their analysis of the split as complementation
against modification is `Studies/BochnakHanink2021.lean`.

## References

* [bochnak-hanink-2021]
* [hanink-2021]
* [jacobsen-1964]
-/

@[expose] public section

namespace Washo

open Morphology (Morph)

/-! ### Clause-typers -/

/-- The clausal nominalizer *-ge*, the accusative form of *-gi ~ -ge* that attitude complements
bear (fn. 6). The clause it closes keeps subject agreement, tense, the independent mood and
switch-reference marking, so it is coded as a finite indicative clause in a nominal shell. -/
def ge : Complementizer where
  morphs := [.suff "ge"]
  coding := some .indicative
  verbForm := some .Fin
  licenser := some .nominal

/-- The dependent mood *-aʔ*, which marks a bare embedded clause and never a matrix clause; the
clause it marks carries no nominalizer and no switch-reference marking (§3.2.1). -/
def aq : Complementizer where
  morphs := [.suff "aʔ"]
  verbForm := some .Fin
  licenser := some .verbal

/-! ### Predicates -/

/-- A Washo complement-taking predicate is a verb entry with the clause-typer of the clause it
embeds. -/
structure Verb extends _root_.Verb where
  /-- The clause-typer on the embedded clause (Table 1). -/
  typer : Complementizer

/-- The negative suffix *-e:s*. -/
def es : Morph := .suff "e:s"

/-- The reflexive prefix *gum-*. -/
def gum : Morph := .pref "gum"

/-- *hamup'ay* 'forget' (1). -/
def hamupay : Verb where
  morphs := [.root "hamup'ay"]
  valency := .ofFrame ArgumentFrame.finiteClause
  typer := ge

/-- *hamup'ay-e:s* 'remember', negated 'forget' (8). -/
def hamupayEs : Verb := { hamupay with morphs := hamupay.morphs ++ [es] }

/-- *ašaš-e:s* 'know', negated 'not know'; it also takes a plain DP ((6), (79)). -/
def ashashEs : Verb where
  morphs := [.root "ašaš", es]
  valency := .of [(ArgumentFrame.finiteClause, [0, 1]), (ArgumentFrame.np, [0, 1])]
  typer := ge

/-- *i:gi* 'see'; it also takes an internally headed relative and a plain DP ((10), (20),
(89)). -/
def iigi : Verb where
  morphs := [.root "i:gi"]
  valency := .of [(ArgumentFrame.finiteClause, [0, 1]), (ArgumentFrame.np, [0, 1])]
  typer := ge

/-- *damal* 'hear', attested only with event nominalizations, the perception reading that needs
no FPROP shift ((11), (84)). -/
def damal : Verb where
  morphs := [.root "damal"]
  valency := .ofFrame ArgumentFrame.finiteClause
  typer := ge

/-- *hamu* 'think', intransitive, questioned with *how* rather than *what* ((2), (49)). -/
def hamu : Verb where
  morphs := [.root "hamu"]
  valency := .ofFrame ArgumentFrame.intransitive
  typer := aq

/-- *i:d* 'say', intransitive ((14), (50)). -/
def iid : Verb where
  morphs := [.root "i:d"]
  valency := .ofFrame ArgumentFrame.intransitive
  typer := aq
  speechActVerb := true

/-- *mɨtgi:bɨl-e:s* 'believe', negated 'disbelieve' (16). -/
def metgiibilEs : Verb where
  morphs := [.root "mɨtgi:bɨl", es]
  valency := .ofFrame ArgumentFrame.intransitive
  typer := aq

/-- *suʔuʔuš* 'dream' without the reflexive, transitive; its nominalized clause is an internally
headed relative ((53), (55)). -/
def suus : Verb where
  morphs := [.root "suʔuʔuš"]
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.finiteClause, [0, 1])]
  typer := ge

/-- *gum-suʔuʔuš* 'dream' with the reflexive, intransitive; its dependent-mood clause is read as a
*that*-clause ((15), (52), (54)). -/
def gumsuus : Verb :=
  { suus with
    morphs := gum :: suus.morphs
    voiceType := some .reflexive
    valency := .ofFrame ArgumentFrame.intransitive
    typer := aq }

/-- The predicates with per-predicate data in the paper. -/
def verbs : List Verb :=
  [hamupay, hamupayEs, ashashEs, iigi, damal, hamu, iid, metgiibilEs, suus, gumsuus]

/-- An intransitive predicate embeds a dependent-mood clause and a transitive one a nominalized
clause (Table 1). -/
theorem typer_eq : ∀ v ∈ verbs, v.typer = if v.toVerb.IsIntransitive then aq else ge := by
  decide

end Washo
