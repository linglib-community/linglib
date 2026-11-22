module

public import Linglib.Fragments.English.Nouns
public import Linglib.Fragments.English.Determiners
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Fragments.English.Auxiliaries
public import Linglib.Fragments.English.Adpositions
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
constituent is a string, hence a component (`isString_of_isConstituent`). The *catena ratio*
of a tree sets its catenae against the remaining $2^n - 1$ word combinations;
`card_units_surprised` and its siblings compute the catenae, components and constituents of the
book's example trees.
The component *the number* of (8) and the 24 catenae of (9a) are counted as the definitions
give them.

The *valency frame* of a verb form lists the valents it can or must take, the subject first and
the objects after it. A finite form takes its subject as a dependent, and the subject valent of
a nonfinite form appears higher in the structure, as a dependent of the finite auxiliary. Here
the valents a form takes as dependents are computed from an argument frame and the form's
finiteness (`dependents`), so a finite form takes those of the nonfinite form and the subject
(`dependents_finite`). The frame of a passive participle is the active frame with its indices
shuffled: the active object is the subject and the active subject the optional object of *by*.
The passive voice's two derived frames, with the demoted subject implicit or in a *by*-phrase,
give the participle the remaining objects and an optional *by*-phrase
(`dependents_passiveFrames`), and its links are the shuffle (`passive_image`). The book's trees
have these dependents verb by verb (`satisfies_trees`, `satisfies_passive`), and the
intransitive use of an ergative verb admits no *by*-phrase (`satisfies_ergative`).

A valent is an *argument* of its carrier when the carrier semantically selects it. A control
predicate selects all its valents and a raising expression has a valent it does not select, the
one that serves as the subject of its verbal valent (`control_selects_valents`,
`raising_subject_not_selected`, `believe_object_not_selected`).

## Implementation notes

The trees are unlabeled, with function words as heads as the book draws them: the subject
depends on the finite auxiliary, a preposition heads its noun. The trees of the valency frames
have the shape of the book's examples over words and verbs of the fragment. The category of a
valent is read off the word that heads it (`category`) and compared with the positions of the
verb's argument frame, so a frame's symbols are not stored: an optional valent is a position
the verb has both an implicit and an expressed diathesis for, the ↑ mark is nonfiniteness, and
an index is the participant a voice links to the position. The book's `R`, a subject of any
category, is a nominal here, the only kind the trees have; the frames of the auxiliaries are
stated in the study, the fragment recording none.

Whether a valent is an argument is read off the diatheses of the fragment's verbs: a valent is
an argument when a participant of the verb fills its slot.

## TODO

* The pseudopassive, which keeps the stranded preposition as a valent, and valents of several
  admissible categories, as the copula's.
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
open Morphology (Word)

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
    #{s ∈ catenae insurance.toGraph | IsString s} = 11 ∧
    #{s | insurance.toGraph.IsConstituent s} = 5 :=
  ⟨by decide, by decide, card_isConstituent insurance.isTree_toGraph.toIsForest⟩

theorem card_units_surprised : #{s : Finset (Fin surprised.size) | IsString s} = 28 ∧
    #(catenae surprised.toGraph) = 28 ∧ #{s ∈ catenae surprised.toGraph | IsString s} = 15 ∧
    #{s | surprised.toGraph.IsConstituent s} = 6 + 1 ∧
    #{s | surprised.toGraph.IsConstituent s ∧ 1 < #s} = 4 + 1 :=
  ⟨by decide, by decide, by decide, card_isConstituent surprised.isTree_toGraph.toIsForest,
    by decide⟩

-- (8) has 44 catenae, 23 components and 8 constituents among its 255 word combinations.
theorem card_units_counting : #(catenae counting.toGraph) = 44 ∧
    #{s ∈ catenae counting.toGraph | IsString s} = 23 ∧
    #{s | counting.toGraph.IsConstituent s} = 8 :=
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

/-! ### Valency frames

A valency frame lists the valents of one form of a verb. The valents a form takes as dependents
are the expressed positions of its argument frame, without the subject when the form is
nonfinite: the subject valent of a nonfinite verb, marked ↑ in the book's frames, appears
higher in the structure. -/

section Frames

open ArgumentFrame (Position)

/-- The valent a word heads: a nominal, the phrase of a preposition, or a verb in its form. -/
def category (w : Word) : Option Position :=
  if w.cat = .NOUN ∨ w.cat = .PROPN ∨ w.cat = .PRON then some .nominal
  else if w.cat = .ADP then
    (English.Adpositions.inventory.find? (·.toWord = w)).map fun a ↦ .adpositional none (some a)
  else if w.cat = .VERB ∨ w.cat = .AUX then
    if w.features .verbForm = ↑UD.VerbForm.Inf then some (.clausal (some .infinitive))
    else if w.features .verbForm = ↑UD.VerbForm.Part then some (.clausal (some .participle))
    else some (.clausal (some .indicative))
  else none

/-- A word is a finite verb form. -/
def IsFinite (w : Word) : Prop := w.features .verbForm = ↑UD.VerbForm.Fin

instance : DecidablePred IsFinite := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- The valents among the dependents of a word. -/
def valents {L : Type*} {n : ℕ} (words : Fin n → Word) (g : Graph L n) (v : Fin n) :
    Multiset Position :=
  (g.children v).val.filterMap fun w ↦ category (words w)

/-- The valents a form of a verb with the frame `fr` takes as dependents: the expressed
positions of the frame, the subject among them only when the form is finite. -/
def dependents (fr : ArgumentFrame) (finite : Prop) [Decidable finite] : Multiset Position :=
  ↑((if finite then fr.external.toList else []) ++ fr.complements.filter (·.IsExpressed))

/-- (5), (6): a finite form takes the dependents of the nonfinite form and the subject. -/
theorem dependents_finite (fr : ArgumentFrame) :
    dependents fr True = ↑fr.external.toList + dependents fr False := by
  simp [dependents]

/-- The word at `v` has the dependents its form takes under one of the frames `frs`. -/
def Satisfies {L : Type*} {n : ℕ} (words : Fin n → Word) (g : Graph L n) (v : Fin n)
    (frs : List ArgumentFrame) : Prop :=
  ∃ fr ∈ frs, valents words g v = dependents fr (IsFinite (words v))

instance {L : Type*} {n : ℕ} (words : Fin n → Word) (g : Graph L n) (v : Fin n)
    (frs : List ArgumentFrame) : Decidable (Satisfies words g v frs) :=
  inferInstanceAs (Decidable (∃ fr ∈ frs, _))

/-- The *by*-phrase of the passive. -/
abbrev byPhrase : Position := .adpositional none (some English.Adpositions.by_)

/-- The frames of the passive participle of a verb with the active frame `fr`, without and with
the *by*-phrase. -/
def passiveFrames (fr : ArgumentFrame) : List ArgumentFrame :=
  [(Voice.passive fr).derived.toArgumentFrame, (Voice.passive fr byPhrase).derived.toArgumentFrame]

/-- (39), (41): an auxiliary takes a subject and a verb in the form it governs. -/
def auxiliaryFrame (c : Clause.ComplementType) : ArgumentFrame :=
  ⟨some .nominal, [.clausal (some c)]⟩

-- (8a): the active object is the passive subject, the active subject the object of *by*.
theorem passive_image : (Voice.passive .np byPhrase).image (.complement 0) = some .external ∧
    (Voice.passive .np byPhrase).image .external = some (.complement 0) := by
  decide

-- (8b): the first object is the passive subject and the second object stays.
theorem passive_image_np_np :
    (Voice.passive .np_np byPhrase).image (.complement 0) = some .external ∧
    (Voice.passive .np_np byPhrase).image (.complement 1) = some (.complement 0) ∧
    (Voice.passive .np_np byPhrase).image .external = some (.complement 1) := by
  decide

/-- (8): the passive participle takes the remaining objects of the active frame and an optional
*by*-phrase. -/
theorem dependents_passiveFrames (fr : ArgumentFrame) (m : Multiset Position) :
    (∃ gr ∈ passiveFrames fr, m = dependents gr False) ↔
      m ∈ Valency.withOptional (↑(fr.complements.tail.filter (·.IsExpressed))) {byPhrase} := by
  have h₁ : [Position.implicit].filter (·.IsExpressed) = [] := by decide
  have h₂ : [byPhrase].filter (·.IsExpressed) = [byPhrase] := by decide
  rw [Valency.mem_withOptional_singleton]
  simp only [passiveFrames, dependents, Voice.passive, Voice.of, List.mem_cons, List.not_mem_nil,
    or_false, exists_eq_or_imp, exists_eq_left, ite_false, List.nil_append, List.filter_append,
    h₁, h₂, List.append_nil, ← Multiset.coe_add, Multiset.coe_singleton]

end Frames

section Trees

open English

abbrev the_ := Determiners.the.toWord
abbrev john := Nouns.john.toWord
abbrev thePizza : Stemma Unit := node Nouns.pizza.toWordSg [((), leaf the_)] []
abbrev theBall : Stemma Unit := node Nouns.ball.toWordSg [((), leaf the_)] []
abbrev byJohn : Stemma Unit := node Adpositions.by_.toWord [] [((), leaf john)]

/-- *John sleeps*, as (5a). -/
def johnSleeps : Stemma Unit := node (Verbs.sleep.toWord .thirdSg) [((), leaf john)] []

/-- *John will sleep*, as (5b): the subject depends on the auxiliary. -/
def johnWillSleep : Stemma Unit :=
  node Auxiliaries.will.toWord [((), leaf john)] [((), leaf (Verbs.sleep.toWord .base))]

/-- *John devours the pizza*, as (6a). -/
def johnDevoursPizza : Stemma Unit :=
  node (Verbs.devour.toWord .thirdSg) [((), leaf john)] [((), thePizza)]

/-- *John should devour the pizza*, as (6b). -/
def johnShouldDevourPizza : Stemma Unit :=
  node Auxiliaries.should.toWord [((), leaf john)]
    [((), node (Verbs.devour.toWord .base) [] [((), thePizza)])]

/-- *The ball was kicked*, as (8a) without the *by*-phrase. -/
def ballWasKicked : Stemma Unit :=
  node Auxiliaries.was.toWord [((), theBall)] [((), leaf Verbs.kick.passiveParticiple)]

/-- *The ball was kicked by John*, as (8a). -/
def ballWasKickedByJohn : Stemma Unit :=
  node Auxiliaries.was.toWord [((), theBall)]
    [((), node Verbs.kick.passiveParticiple [] [((), byJohn)])]

/-- *Mary was given a book*, as (8b). -/
def maryWasGivenBook : Stemma Unit :=
  node Auxiliaries.was.toWord [((), leaf Nouns.mary.toWord)]
    [((), node Verbs.give.passiveParticiple []
      [((), node Nouns.book.toWordSg [((), leaf Determiners.a.toWord)] [])])]

/-- *The ball opened*, the intransitive use of an ergative verb. -/
def ballOpened : Stemma Unit := node (Verbs.open_.toWord .past) [((), theBall)] []

/-- *The ball opened by John* adds the *by*-phrase of a passive to the intransitive use. -/
def ballOpenedByJohn : Stemma Unit :=
  node (Verbs.open_.toWord .past) [((), theBall)] [((), byJohn)]

/-- *John sleeps the pizza* adds an object to the intransitive. -/
def johnSleepsPizza : Stemma Unit :=
  node (Verbs.sleep.toWord .thirdSg) [((), leaf john)] [((), thePizza)]

/-- *Was the ball kicked* with the subject a dependent of the participle. -/
def wasBallKicked : Stemma Unit :=
  node Auxiliaries.was.toWord [] [((), node Verbs.kick.passiveParticiple [((), theBall)] [])]

theorem satisfies_trees :
    Satisfies johnSleeps.word johnSleeps.toGraph 1 Verbs.sleep.valency.frames ∧
    Satisfies johnWillSleep.word johnWillSleep.toGraph 1 [auxiliaryFrame .infinitive] ∧
    Satisfies johnWillSleep.word johnWillSleep.toGraph 2 Verbs.sleep.valency.frames ∧
    Satisfies johnDevoursPizza.word johnDevoursPizza.toGraph 1 Verbs.devour.valency.frames ∧
    Satisfies johnShouldDevourPizza.word johnShouldDevourPizza.toGraph 1
      [auxiliaryFrame .infinitive] ∧
    Satisfies johnShouldDevourPizza.word johnShouldDevourPizza.toGraph 2
      Verbs.devour.valency.frames := by
  decide

/-- The passive participle under its auxiliary has the dependents of a passive frame, with or
without the *by*-phrase. -/
theorem satisfies_passive :
    Satisfies ballWasKicked.word ballWasKicked.toGraph 2 [auxiliaryFrame .participle] ∧
    Satisfies ballWasKicked.word ballWasKicked.toGraph 3
      (Verbs.kick.valency.frames.flatMap passiveFrames) ∧
    Satisfies ballWasKickedByJohn.word ballWasKickedByJohn.toGraph 3
      (Verbs.kick.valency.frames.flatMap passiveFrames) ∧
    Satisfies maryWasGivenBook.word maryWasGivenBook.toGraph 2
      (Verbs.give.valency.frames.flatMap passiveFrames) := by
  decide

-- An ergative verb's intransitive use has no *by*-phrase.
theorem satisfies_ergative :
    Satisfies ballOpened.word ballOpened.toGraph 2 Verbs.open_.valency.frames ∧
    ¬ Satisfies ballOpenedByJohn.word ballOpenedByJohn.toGraph 2 Verbs.open_.valency.frames := by
  decide

example : ¬ Satisfies johnSleepsPizza.word johnSleepsPizza.toGraph 1
    Verbs.sleep.valency.frames := by decide

-- A participle with a subject dependent has a valent too many, and its auxiliary one too few.
example : ¬ Satisfies wasBallKicked.word wasBallKicked.toGraph 3
      (Verbs.kick.valency.frames.flatMap passiveFrames) ∧
    ¬ Satisfies wasBallKicked.word wasBallKicked.toGraph 0 [auxiliaryFrame .participle] := by
  decide

end Trees

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
