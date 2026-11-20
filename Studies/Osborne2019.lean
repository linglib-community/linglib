module

public import Linglib.Fragments.English.Nouns
public import Linglib.Fragments.English.Determiners
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Fragments.English.Auxiliaries
public import Linglib.Fragments.English.Adpositions
public import Linglib.Data.UD.DepRel
public import Linglib.Syntax.DependencyGrammar.Valency
public import Linglib.Syntax.Voice.Basic
public import Linglib.Syntax.DependencyGrammar.Catena
public import Linglib.Syntax.DependencyGrammar.Basic

/-!
# Osborne (2019): A Dependency Grammar of English

This file formalizes the parts of the dependency grammar of [osborne-2019] that the English fragment
lexicon supports. A verb's valency frame (sixth chapter) lists the valents it can or must take
and is a lexical property, read here off the argument roles of the fragment's basic frame. The
passive participle's frame is not listed but related to the active one by a shuffle of indices,
the passive voice moving the active's participants, with the demoted subject an optional
*by*-phrase (`voiceValency_passive`); an ergative verb's intransitive use suppresses the agent
instead and has no *by*-phrase (`voiceValency_anticausative`), so its valency lies within the
passive's (`voiceValency_anticausative_le_passive`). Trees over fragment words satisfy their
frames; a spurious or a missing object, a second subject, and a *by*-phrase with an ergative
intransitive violate them. The catena (fourth chapter), any set of words connected by
dominance, is the unit that constituents do not always match: every constituent is a catena,
a head with one of its dependents is always a catena, and it is never a constituent when the
head has another dependent, so a verb with its subject but not its object is a catena and not
a constituent (`IsConstituent.isCatena`, `Graph.isCatena_pair`, `Graph.not_isConstituent_pair`); that is
the material gapping elides (§12.7). Control and raising (§6.8, §6.9) share one basic tree,
whose embedded verb lacks a subject; the enhanced graph adds the subject arc, which the basic
tree cannot carry without ceasing to be a tree (`Graph.hasUnrepresentedArg_enhance`,
`Graph.not_isForest_enhance`).

## Implementation notes

The trees are Universal Dependencies graphs over fragment words after [tesniere-1959], and
the enhanced graph is the basic tree with the recovered subject arc added; the general lemmas
live in the dependency-grammar substrate and are instantiated here on the fragment trees. The
UD trees make the subject of a passive participle its dependent, where [osborne-2019]'s
function-word-headed trees mark it with ↑ as a dependent of the finite auxiliary.

The valents of [osborne-2019]'s frames are syntactic categories with an index and a preposition;
here a valent is the UD relation of the dependent, a nominal valent being a subject, an object,
an indirect object or an oblique (`IsValentRel`). UD's oblique covers adjunct phrases as well as
the *by*-phrase and prepositional objects, so a tree with an adjunct oblique would count it
among the valents; the trees here have none.

## References

* [osborne-2019]
* [tesniere-1959]
-/

@[expose] public section

namespace Osborne2019

open DependencyGrammar
open Morphology (Word)

/-! ### Words from the Fragment lexicon -/

abbrev john := English.Nouns.john.toWord
abbrev mary := English.Nouns.mary.toWord
abbrev ball := English.Nouns.ball.toWordSg
abbrev book := English.Nouns.book.toWordSg
abbrev pizza := English.Nouns.pizza.toWordSg
abbrev the_ := English.Determiners.the.toWord
abbrev was_ := English.Auxiliaries.was.toWord
abbrev by_ := English.Adpositions.by_.toWord
abbrev to_ := English.Adpositions.to_.toWord
abbrev sleeps := English.Verbs.sleep.toWord .thirdSg
abbrev devours := English.Verbs.devour.toWord .thirdSg
abbrev gives := English.Verbs.give.toWord .thirdSg
private abbrev kicked := English.Verbs.kick.toWord .past
abbrev kickedPass := English.Verbs.kick.passiveParticiple
abbrev givenPass := English.Verbs.give.passiveParticiple
abbrev a_ := English.Determiners.a.toWord
abbrev manages := English.Verbs.manage.toWord .thirdSg
abbrev persuaded := English.Verbs.persuade.toWord .past
abbrev seems := English.Verbs.seem.toWord .thirdSg
abbrev sleep_ := English.Verbs.sleep.toWord .base
abbrev run_ := English.Verbs.run.toWord .base
abbrev opened := English.Verbs.open_.toWord .past

/-! ### Valency frames from the Fragment (sixth chapter) -/

/-- The relation a core argument bears to its verb in the trees: S and A are the subject, P and
T the object, and R the indirect object. -/
def relation : ArgumentRole → UD.DepRel
  | .S | .A => .nsubj
  | .P | .T => .obj
  | .R => .iobj

/-- The relations of the core arguments of a frame. -/
def coreRelations (fr : ArgumentFrame) : Multiset UD.DepRel :=
  ↑(fr.coreSlots.filterMap fun s ↦ (fr.argumentRole s).map relation)

/-- The frames of (4a) to (4c): a monovalent verb takes a subject, a divalent verb a subject and
an object, and a trivalent verb a subject and two objects. -/
theorem coreRelations_basic : coreRelations .intransitive = {.nsubj} ∧
    coreRelations .np = {.nsubj, .obj} ∧ coreRelations .np_np = {.nsubj, .iobj, .obj} := by
  decide

/-- The relations of nominal valents in the trees are the nominal core arguments and the
oblique. -/
def IsValentRel (r : UD.DepRel) : Prop := r.kind = .cell .core .nominal ∨ r = .obl

instance : DecidablePred IsValentRel := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The valency of the fragment entry's basic frame, every valent obligatory. -/
private def citationValency (v : English.Verbs.Verb) : Valency UD.DepRel :=
  .pure ((v.valency.frames.head?.map coreRelations).getD 0)

def intransTree : Graph UD.DepRel 2 := .ofArcs [john, sleeps] 1 [(1, 0, .nsubj)]

def transTree : Graph UD.DepRel 3 :=
  .ofArcs [john, devours, pizza] 1 [(1, 0, .nsubj), (1, 2, .obj)]

def ditransTree : Graph UD.DepRel 4 :=
  .ofArcs [john, gives, mary, book] 1 [(1, 0, .nsubj), (1, 2, .iobj), (1, 3, .obj)]

example : intransTree.Satisfies IsValentRel 1 (citationValency English.Verbs.sleep) := by decide
example : transTree.Satisfies IsValentRel 1 (citationValency English.Verbs.devour) := by decide
example : ditransTree.Satisfies IsValentRel 1 (citationValency English.Verbs.give) := by decide

/-- *John sleeps book, an intransitive with a spurious object. -/
def intransWithObj : Graph UD.DepRel 3 :=
  .ofArcs [john, sleeps, book] 1 [(1, 0, .nsubj), (1, 2, .obj)]

/-- *John devours, a transitive missing its object. -/
def transNoObj : Graph UD.DepRel 2 := .ofArcs [john, devours] 1 [(1, 0, .nsubj)]

/-- *John Mary sleeps, an intransitive with two subjects. -/
def intransTwoSubj : Graph UD.DepRel 3 :=
  .ofArcs [john, mary, sleeps] 2 [(2, 0, .nsubj), (2, 1, .nsubj)]

example : ¬ intransWithObj.Satisfies IsValentRel 1 (citationValency English.Verbs.sleep) := by
  decide
example : ¬ transNoObj.Satisfies IsValentRel 1 (citationValency English.Verbs.devour) := by
  decide
example : ¬ intransTwoSubj.Satisfies IsValentRel 2 (citationValency English.Verbs.sleep) := by
  decide

/-! ### The passive frame from the active frame (§6.6)

The passive participle's frame is not listed but related to the active frame by a shuffle of
indices, (8): the active object is the subject and the active subject the optional object of
*by*. The shuffle is the passive voice's links of its participants, and the *by*-phrase
realizes the participant it denucleativizes. The intransitive use of an ergative verb, *It
opened*, also makes the object the subject, but it suppresses the agent, and no *by*-phrase
expresses it. -/

/-- The valency of the construction a voice derives: the core arguments of its derived frame are
obligatory, and there is an optional oblique, the *by*-phrase, for each initial core term the
voice denucleativizes. -/
def voiceValency (v : Voice) : Valency UD.DepRel :=
  .withOptional (coreRelations v.derived.toArgumentFrame)
    (.replicate (v.initial.coreSlots.countP (v.fate · = .denucleativized)) .obl)

/-- In (8a) the English passive has the subject and an optional *by*-phrase. -/
theorem voiceValency_passive :
    voiceValency English.Verbs.passive = .withOptional {.nsubj} {.obl} := by
  decide

/-- In (8b) the passive of a double-object verb keeps its second object. -/
theorem voiceValency_passive_np_np :
    voiceValency (Voice.passive .np_np) = .withOptional {.nsubj, .obj} {.obl} := by
  decide

/-- The intransitive use of an ergative verb has its subject and no *by*-phrase. -/
theorem voiceValency_anticausative : English.Verbs.open_.Alternates Voice.anticausative ∧
    voiceValency Voice.anticausative = .pure {.nsubj} := by
  decide

/-- The valency of the fragment entry's passive participle. -/
private def passiveValency (v : English.Verbs.Verb) : Valency UD.DepRel :=
  (v.valency.frames.head?.map fun fr ↦ voiceValency (Voice.passive fr)).getD (.pure 0)

/-- *The ball was kicked (by John)* satisfies the participle's derived valency. -/
def passiveTree : Graph UD.DepRel 4 :=
  .ofArcs [the_, ball, was_, kickedPass] 3 [(1, 0, .det), (3, 1, .nsubj), (3, 2, .aux)]

def longPassiveTree : Graph UD.DepRel 6 :=
  .ofArcs [the_, ball, was_, kickedPass, by_, john] 3
    [(1, 0, .det), (3, 1, .nsubj), (3, 2, .aux), (3, 5, .obl), (5, 4, .case)]

example : passiveTree.Satisfies IsValentRel 3 (passiveValency English.Verbs.kick) := by decide
example : longPassiveTree.Satisfies IsValentRel 3 (passiveValency English.Verbs.kick) := by
  decide

/-- *The ball was kicked the pizza, a passive with a leftover object. -/
def passiveWithObj : Graph UD.DepRel 6 :=
  .ofArcs [the_, ball, was_, kickedPass, the_, pizza] 3
    [(1, 0, .det), (3, 1, .nsubj), (3, 2, .aux), (3, 5, .obj), (5, 4, .det)]

example : ¬ passiveWithObj.Satisfies IsValentRel 3 (passiveValency English.Verbs.kick) := by
  decide

/-- In *Mary was given a book* the passive of a double-object verb keeps its second object. -/
def ditransPassiveTree : Graph UD.DepRel 5 :=
  .ofArcs [mary, was_, givenPass, a_, book] 2
    [(2, 0, .nsubj), (2, 1, .aux), (2, 4, .obj), (4, 3, .det)]

/-- *Mary was given, with the second object missing. -/
def ditransPassiveNoObj : Graph UD.DepRel 3 :=
  .ofArcs [mary, was_, givenPass] 2 [(2, 0, .nsubj), (2, 1, .aux)]

example : ditransPassiveTree.Satisfies IsValentRel 2 (passiveValency English.Verbs.give) := by
  decide
example : ¬ ditransPassiveNoObj.Satisfies IsValentRel 2 (passiveValency English.Verbs.give) := by
  decide

/-- *The ball opened* satisfies the valency of the ergative verb's intransitive use. -/
def ergativeTree : Graph UD.DepRel 3 :=
  .ofArcs [the_, ball, opened] 2 [(1, 0, .det), (2, 1, .nsubj)]

/-- *The ball opened by John, the intransitive use with the *by*-phrase of a passive. -/
def ergativeWithBy : Graph UD.DepRel 5 :=
  .ofArcs [the_, ball, opened, by_, john] 2
    [(1, 0, .det), (2, 1, .nsubj), (2, 4, .obl), (4, 3, .case)]

example : ergativeTree.Satisfies IsValentRel 2 (voiceValency Voice.anticausative) := by decide

/-- The valency of the intransitive use lies within the passive's, so whatever satisfies the
first satisfies the second. -/
theorem voiceValency_anticausative_le_passive :
    voiceValency Voice.anticausative ≤ voiceValency English.Verbs.passive := by
  decide

example : ergativeTree.Satisfies IsValentRel 2 (voiceValency English.Verbs.passive) :=
  .mono voiceValency_anticausative_le_passive (by decide)

/-- The same dependents that the passive's valency admits, a subject and a *by*-phrase, the
valency of the intransitive use rejects. -/
example : ergativeWithBy.Satisfies IsValentRel 2 (voiceValency English.Verbs.passive) ∧
    ¬ ergativeWithBy.Satisfies IsValentRel 2 (voiceValency Voice.anticausative) := by
  decide

/-! ### Catenae against constituents (fourth chapter, §12.7)

In *John devours pizza* the verb with its subject is a catena, being a head with a dependent,
but not a constituent, since the verb has another dependent; the whole clause and the object
are constituents and therefore catenae. The verb with its subject is what gapping elides in
*John devours pizza and Mary wine*. -/

example : transTree.IsCatena {1, 0} := Graph.isCatena_pair transTree (by decide) (by decide)

example : ¬ transTree.IsConstituent {1, 0} :=
  Graph.not_isConstituent_pair (u := 2) (by decide) (by decide) (by decide) (by decide)

example : transTree.IsCatena {0, 1, 2} :=
  (show transTree.IsConstituent {0, 1, 2} by decide).isCatena

example : transTree.IsCatena {2} := (show transTree.IsConstituent {2} by decide).isCatena

example : ¬ transTree.IsCatena {0, 2} := by decide

/-! ### Control and raising (§6.8, §6.9)

The basic tree of *John manages to sleep*, *John persuaded Mary to run*, and *John seems to
sleep* leaves the embedded verb without a subject; control and raising differ thematically,
not structurally. The enhanced graph recovers the subject arc, an argument relation the
basic tree does not carry and cannot, since a second head breaks the tree. -/

def subjControl : Graph UD.DepRel 4 :=
  .ofArcs [john, manages, to_, sleep_] 1 [(1, 0, .nsubj), (1, 3, .xcomp), (3, 2, .mark)]

def objControl : Graph UD.DepRel 5 :=
  .ofArcs [john, persuaded, mary, to_, run_] 1
    [(1, 0, .nsubj), (1, 2, .obj), (1, 4, .xcomp), (4, 3, .mark)]

def raising : Graph UD.DepRel 4 :=
  .ofArcs [john, seems, to_, sleep_] 1 [(1, 0, .nsubj), (1, 3, .xcomp), (3, 2, .mark)]

example : Graph.HasUnrepresentedArg subjControl (subjControl.enhance [(3, 0, .nsubj)]) 0 :=
  Graph.hasUnrepresentedArg_enhance _ (x := 3) .nsubj _ (by simp) (by decide)

example : Graph.HasUnrepresentedArg objControl (objControl.enhance [(4, 2, .nsubj)]) 2 :=
  Graph.hasUnrepresentedArg_enhance _ (x := 4) .nsubj _ (by simp) (by decide)

example : Graph.HasUnrepresentedArg raising (raising.enhance [(3, 0, .nsubj)]) 0 :=
  Graph.hasUnrepresentedArg_enhance _ (x := 3) .nsubj _ (by simp) (by decide)

example : ¬ (subjControl.enhance [(3, 0, .nsubj)]).IsTree := fun hT ↦
  Graph.not_isForest_enhance (v := 1) (w := 0) (x := 3) (by decide) (by decide) .nsubj _ (by simp)
    hT.toIsForest

end Osborne2019
