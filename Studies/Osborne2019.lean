module

public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Data.UD.DepRel
public import Linglib.Syntax.DependencyGrammar.Valency
public import Linglib.Syntax.Voice.Basic
public import Linglib.Syntax.DependencyGrammar.Catena
public import Linglib.Syntax.DependencyGrammar.Stemma

/-!
# Osborne (2019): A Dependency Grammar of English

[osborne-2019] builds a dependency grammar of English on two orders over the words of a
sentence, precedence and dominance. This file formalizes its units of structure and its valency
frames.

A *string* is a word or a combination of words continuous with respect to precedence, and a
*catena* one continuous with respect to dominance; a *component* is both, a *constituent* is a
word together with all the words it dominates, and a *phrase* is a constituent of two or more
words. In a tree, a catena is equally a set of words exactly one of which is not immediately
dominated by another word of the set, which is how `catenae` counts them (`mem_catenae`). A
tree has as many constituents as words (`card_isConstituent`), and when it is projective every
constituent is a string, hence a component (`isString_of_isConstituent`). The *catena ratio* of a tree
sets its catenae against the remaining $2^n - 1$ word combinations; `card_units_surprised` and
its siblings compute the catenae, components and constituents of the book's example trees.
The component *the number* of (8) and the 24 catenae of (9a) are counted as the definitions
give them.

The *valency frame* of a verb lists the valents it can or must take, the subject first and the
objects after it. The frame of a passive participle is the active frame with its indices
shuffled: the active object is the subject and the active subject the optional object of *by*.
Here `voiceValency` computes the frame of the construction a voice derives, and the passive
(`voiceValency_passive`) and the intransitive use of an ergative verb
(`voiceValency_anticausative`) come out as the book gives them, the second lying within the
first (`voiceValency_anticausative_le_passive`). A valent is an *argument* of its carrier when
the carrier semantically selects it. A control predicate selects all its valents and a raising
expression has a valent it does not select, the one that serves as the subject of its verbal
valent (`control_selects_valents`, `raising_subject_not_selected`,
`believe_object_not_selected`).

## Implementation notes

The trees of the units of structure are the book's, unlabeled and with function words as heads.
The trees of the valency frames are Universal Dependencies trees, and the frames are those of
verbs of the fragment standing in the book's. A valent is the relation its dependent
bears, a nominal valent being a subject, an object, an indirect object or an oblique
(`IsValentRel`), where the book's valents are syntactic categories ranked by grammatical
function; the UD trees make the subject of a participle its dependent, where the book marks it
with ↑ as a dependent of the finite auxiliary. UD's oblique covers adjunct phrases as well as
the *by*-phrase, so a tree with an adjunct oblique would count it among the valents; the trees
here have none. The sentences that violate a frame are built from the satisfying ones by adding
or removing a dependent.

Whether a valent is an argument is read off the diatheses of the fragment's verbs: a valent is
an argument when a participant of the verb fills its slot.

## TODO

* The frames of prepositional valents and of the pseudopassive, which keeps the stranded
  preposition as a valent.
* The *there* diagnostic for raising, an expletive standing only where a valent is not an
  argument; the fragment has no infinitival diathesis for *refuse*, *appear*, *tell* or *deem*,
  the verbs of the book's examples.

## References

* [osborne-2019]
-/

@[expose] public section

namespace Osborne2019

open DependencyGrammar Finset
open Stemma (node leaf)

/-! ### Units of structure -/

section Units

variable {L : Type*} {n : ℕ} (g : Graph L n)

/-- A string is a word or a combination of words continuous with respect to precedence. -/
def IsString (s : Finset (Fin n)) : Prop := s.Nonempty ∧ (↑s : Set (Fin n)).OrdConnected

instance : DecidablePred (IsString (n := n)) := fun s ↦
  decidable_of_iff (s.Nonempty ∧ ∀ a ∈ s, ∀ b ∈ s, ∀ c, a ≤ c → c ≤ b → c ∈ s) <| by
    simp [IsString, Set.ordConnected_def, Set.subset_def]

/-- The sets of words exactly one of which is not immediately dominated by another word of the
set. -/
def catenae : Finset (Finset (Fin n)) := {s | #{v ∈ s | ∀ u ∈ s, ¬ g.Adj u v} = 1}

variable {g} {s : Finset (Fin n)}

/-- In a forest the set-theoretic definition of the catena picks out the sets of words
continuous with respect to dominance. -/
theorem mem_catenae (hF : g.IsForest) : s ∈ catenae g ↔ g.IsCatena s := by
  simp [catenae, hF.isCatena_iff]

-- In a projective graph a constituent is a string, and so a component.
theorem isString_of_isConstituent (hP : g.IsProjective) (h : g.IsConstituent s) : IsString s := by
  obtain ⟨v, hv⟩ := h
  exact ⟨⟨v, Finset.mem_coe.1 (hv ▸ Relation.ReflTransGen.refl)⟩, hv ▸ hP v⟩

/-- A forest has as many constituents as words. -/
theorem card_isConstituent (hF : g.IsForest) : #{s : Finset (Fin n) | g.IsConstituent s} = n :=
  hF.card_isConstituent

end Units

/-- (6) of the fourth chapter, *Catenae are everywhere*. -/
def everywhere : Stemma Unit :=
  node (.mk' "are" .AUX) [((), leaf (.mk' "Catenae" .NOUN))] [((), leaf (.mk' "everywhere" .ADV))]

/-- (7) of the fourth chapter, *Insurance for everyone is possible*. -/
def insurance : Stemma Unit :=
  node (.mk' "is" .AUX)
    [((), node (.mk' "Insurance" .NOUN) []
      [((), node (.mk' "for" .ADP) [] [((), leaf (.mk' "everyone" .PRON))])])]
    [((), leaf (.mk' "possible" .ADJ))]

/-- (4) of the fourth chapter, *That the students understood surprised the instructor*. -/
def surprised : Stemma Unit :=
  node (.mk' "surprised" .VERB)
    [((), node (.mk' "That" .SCONJ) []
      [((), node (.mk' "understood" .VERB)
        [((), node (.mk' "students" .NOUN) [((), leaf (.mk' "the" .DET))] [])] [])])]
    [((), node (.mk' "instructor" .NOUN) [((), leaf (.mk' "the" .DET))] [])]

/-- (8) of the fourth chapter, *Counting the number of catenae can be tedious*. -/
def counting : Stemma Unit :=
  node (.mk' "can" .AUX)
    [((), node (.mk' "Counting" .VERB) []
      [((), node (.mk' "number" .NOUN) [((), leaf (.mk' "the" .DET))]
        [((), node (.mk' "of" .ADP) [] [((), leaf (.mk' "catenae" .NOUN))])])])]
    [((), node (.mk' "be" .AUX) [] [((), leaf (.mk' "tedious" .ADJ))])]

/-- (9a) of the fourth chapter, *Many people favor the public option*. -/
def favor : Stemma Unit :=
  node (.mk' "favor" .VERB)
    [((), node (.mk' "people" .NOUN) [((), leaf (.mk' "Many" .ADJ))] [])]
    [((), node (.mk' "option" .NOUN)
      [((), leaf (.mk' "the" .DET)), ((), leaf (.mk' "public" .ADJ))] [])]

-- The catena ratio of (6) is 6:1.
theorem card_catenae_everywhere : #(catenae everywhere.toGraph) = 6 := by decide

-- The catena, component and constituent ratios of (7) are 15:16, 11:20 and 5:26.
theorem card_units_insurance : #(catenae insurance.toGraph) = 15 ∧
    #{s ∈ catenae insurance.toGraph | IsString s} = 11 ∧ #{s | insurance.toGraph.IsConstituent s} = 5 :=
  ⟨by decide, by decide, card_isConstituent insurance.isTree_toGraph.toIsForest⟩

theorem card_units_surprised : #{s : Finset (Fin surprised.size) | IsString s} = 28 ∧
    #(catenae surprised.toGraph) = 28 ∧ #{s ∈ catenae surprised.toGraph | IsString s} = 15 ∧
    #{s | surprised.toGraph.IsConstituent s} = 6 + 1 ∧ #{s | surprised.toGraph.IsConstituent s ∧ 1 < #s} = 4 + 1 :=
  ⟨by decide, by decide, by decide, card_isConstituent surprised.isTree_toGraph.toIsForest,
    by decide⟩

-- (8) has 44 catenae, 23 components and 8 constituents among its 255 word combinations.
theorem card_units_counting : #(catenae counting.toGraph) = 44 ∧
    #{s ∈ catenae counting.toGraph | IsString s} = 23 ∧ #{s | counting.toGraph.IsConstituent s} = 8 :=
  ⟨by decide, by decide, card_isConstituent counting.isTree_toGraph.toIsForest⟩

-- (9a) has 24 catenae, 14 components and 6 constituents among its 63 word combinations.
theorem card_units_favor : #(catenae favor.toGraph) = 24 ∧
    #{s ∈ catenae favor.toGraph | IsString s} = 14 ∧ #{s | favor.toGraph.IsConstituent s} = 6 :=
  ⟨by decide, by decide, card_isConstituent favor.isTree_toGraph.toIsForest⟩

-- In (4) the verb with its subordinator is a catena and not a string, the determiner with the
-- verb before it a string and not a catena, and the subject clause a phrase.
example : ({0, 3} : Finset (Fin surprised.size)) ∈ catenae surprised.toGraph ∧
    ¬ IsString ({0, 3} : Finset (Fin surprised.size)) := by decide
example : IsString ({3, 4} : Finset (Fin surprised.size)) ∧
    ({3, 4} : Finset (Fin surprised.size)) ∉ catenae surprised.toGraph := by decide
example : surprised.toGraph.IsConstituent {0, 1, 2, 3} := by decide

/-! ### Valency frames from the fragment -/

/-- The relation a core argument bears to its verb in the trees: S and A are the subject, P and
T the object, and R the indirect object. -/
def relation : ArgumentRole → UD.DepRel
  | .S | .A => .nsubj
  | .P | .T => .obj
  | .R => .iobj

/-- The relations of the core arguments of a frame. -/
def coreRelations (fr : ArgumentFrame) : Multiset UD.DepRel :=
  ↑(fr.coreSlots.filterMap fun s ↦ (fr.argumentRole s).map relation)

-- (4a), (4c)
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

def intransTree : Graph UD.DepRel 2 := .ofArcs 1 [(1, 0, .nsubj)]

def transTree : Graph UD.DepRel 3 :=
  .ofArcs 1 [(1, 0, .nsubj), (1, 2, .obj)]

def ditransTree : Graph UD.DepRel 4 :=
  .ofArcs 1 [(1, 0, .nsubj), (1, 2, .iobj), (1, 3, .obj)]

example : intransTree.Satisfies IsValentRel 1 (citationValency English.Verbs.sleep) := by decide
example : transTree.Satisfies IsValentRel 1 (citationValency English.Verbs.devour) := by decide
example : ditransTree.Satisfies IsValentRel 1 (citationValency English.Verbs.give) := by decide

/-- *John sleeps book* adds an object to the intransitive. -/
def intransWithObj : Graph UD.DepRel 3 :=
  .ofArcs 1 [(1, 0, .nsubj), (1, 2, .obj)]

/-- *John devours* removes the object of the transitive. -/
def transNoObj : Graph UD.DepRel 2 := .ofArcs 1 [(1, 0, .nsubj)]

/-- *John Mary sleeps* adds a second subject to the intransitive. -/
def intransTwoSubj : Graph UD.DepRel 3 :=
  .ofArcs 2 [(2, 0, .nsubj), (2, 1, .nsubj)]

example : ¬ intransWithObj.Satisfies IsValentRel 1 (citationValency English.Verbs.sleep) := by
  decide
example : ¬ transNoObj.Satisfies IsValentRel 1 (citationValency English.Verbs.devour) := by
  decide
example : ¬ intransTwoSubj.Satisfies IsValentRel 2 (citationValency English.Verbs.sleep) := by
  decide

/-! ### The passive frame from the active frame

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

-- (8b)
theorem voiceValency_passive_np_np :
    voiceValency (Voice.passive .np_np) = .withOptional {.nsubj, .obj} {.obl} := by
  decide

theorem voiceValency_anticausative : English.Verbs.open_.Alternates Voice.anticausative ∧
    voiceValency Voice.anticausative = .pure {.nsubj} := by
  decide

/-- The valency of the fragment entry's passive participle. -/
private def passiveValency (v : English.Verbs.Verb) : Valency UD.DepRel :=
  (v.valency.frames.head?.map fun fr ↦ voiceValency (Voice.passive fr)).getD (.pure 0)

/-- *The ball was kicked (by John)* satisfies the participle's derived valency. -/
def passiveTree : Graph UD.DepRel 4 :=
  .ofArcs 3 [(1, 0, .det), (3, 1, .nsubj), (3, 2, .aux)]

def longPassiveTree : Graph UD.DepRel 6 :=
  .ofArcs 3
    [(1, 0, .det), (3, 1, .nsubj), (3, 2, .aux), (3, 5, .obl), (5, 4, .case)]

example : passiveTree.Satisfies IsValentRel 3 (passiveValency English.Verbs.kick) := by decide
example : longPassiveTree.Satisfies IsValentRel 3 (passiveValency English.Verbs.kick) := by
  decide

/-- *The ball was kicked the pizza* adds an object to the passive. -/
def passiveWithObj : Graph UD.DepRel 6 :=
  .ofArcs 3
    [(1, 0, .det), (3, 1, .nsubj), (3, 2, .aux), (3, 5, .obj), (5, 4, .det)]

example : ¬ passiveWithObj.Satisfies IsValentRel 3 (passiveValency English.Verbs.kick) := by
  decide

/-- In *Mary was given a book* the passive of a double-object verb keeps its second object. -/
def ditransPassiveTree : Graph UD.DepRel 5 :=
  .ofArcs 2
    [(2, 0, .nsubj), (2, 1, .aux), (2, 4, .obj), (4, 3, .det)]

/-- *Mary was given* removes the second object. -/
def ditransPassiveNoObj : Graph UD.DepRel 3 :=
  .ofArcs 2 [(2, 0, .nsubj), (2, 1, .aux)]

example : ditransPassiveTree.Satisfies IsValentRel 2 (passiveValency English.Verbs.give) := by
  decide
example : ¬ ditransPassiveNoObj.Satisfies IsValentRel 2 (passiveValency English.Verbs.give) := by
  decide

/-- *The ball opened* satisfies the valency of the ergative verb's intransitive use. -/
def ergativeTree : Graph UD.DepRel 3 :=
  .ofArcs 2 [(1, 0, .det), (2, 1, .nsubj)]

/-- *The ball opened by John* adds the *by*-phrase of a passive to the intransitive use. -/
def ergativeWithBy : Graph UD.DepRel 5 :=
  .ofArcs 2
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

/-! ### Control and raising

A valent is an argument of its carrier when a participant of the carrier fills its slot. The
frames of *try*, *want* and *persuade* have only arguments, the controller among them; *seem*
and *happen* raise into a subject that is no argument of theirs, and *believe* with an
infinitive into such an object. -/

open English.Verbs in
theorem control_selects_valents : ∀ v ∈ [try_, want, persuade], ∀ d ∈ v.valency.basic?,
    ¬ d.IsRaising ∧ ∀ s ∈ d.slots, d.participantAt s ≠ none := by
  decide

open English.Verbs in
/-- The subject of a subject-raising verb is the one valent the verb does not select, and it
serves as the subject of the verbal valent. -/
theorem raising_subject_not_selected : ∀ v ∈ [seem, happen], ∀ d ∈ v.valency.basic?,
    d.IsRaising ∧ d.controllerSlot? = some .external ∧
      ∀ s ∈ d.slots, d.participantAt s = none ↔ s = .external := by
  decide

open English.Verbs in
theorem believe_object_not_selected : ∃ d ∈ believe.valency.diatheses,
    d.IsRaising ∧ d.controllerSlot? = some (.complement 0) ∧
      ∀ s ∈ d.slots, d.participantAt s = none ↔ s = .complement 0 := by
  decide

end Osborne2019
