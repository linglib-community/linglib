module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.DeriveFintype

/-!
# Universal Dependencies: syntactic relations

Universal Dependencies v2 labels each arc of a dependency tree with one of 37 universal syntactic
relations. De Marneffe, Manning, Nivre and Zeman organize them in a typology. A relation of its
main table pairs a functional category, the dependent's relation to its head, with a structural
category, the dependent's form. The remaining relations, which are not dependency relations in
the narrow sense, fall into five groups.

## Main definitions

* `UD.DepRel`: the universal relations.
* `UD.DepRel.kind`: the place of a relation in the typology.
* `UD.DepRel.IsCore`: the core-argument relations.

## Implementation notes

A language-specific subtype such as `nsubj:pass` or `acl:relcl` refines a universal relation after
a colon. Labels here are universal relations, so a passive subject is `nsubj` and a passive
auxiliary `aux`.

## References

* [de-marneffe-zeman-2021]
-/

@[expose] public section

namespace UD

/-- The universal syntactic relations of Universal Dependencies. -/
inductive DepRel where
  /-- A finite or non-finite clause modifying a nominal. -/
  | acl
  /-- An adverbial clause modifying a predicate or modifier word. -/
  | advcl
  /-- An adverb or adverbial phrase modifying a predicate or modifier word. -/
  | advmod
  /-- An adjectival modifier of a nominal. -/
  | amod
  /-- A nominal that defines, names or describes the referent of a preceding nominal. -/
  | appos
  /-- A function word expressing tense, mood, aspect, voice or evidentiality on a predicate. -/
  | aux
  /-- A case-marking element of a nominal, such as a preposition, postposition or clitic, with the
  label `case`. -/
  | case_
  /-- A coordinating conjunction, attached to the following conjunct. -/
  | cc
  /-- A clausal complement of a verb or adjective without an obligatorily controlled subject. -/
  | ccomp
  /-- A classifier of nouns, linked to a numeric modifier or determiner. -/
  | clf
  /-- Word-level compounding of any kind, such as a noun compound, serial verb or phrasal verb. -/
  | compound
  /-- A conjunct, attached to the first conjunct. -/
  | conj
  /-- A function word connecting a subject to a nonverbal predicate. -/
  | cop
  /-- A clausal syntactic subject of a predicate. -/
  | csubj
  /-- An unspecified dependency, used when a more precise relation cannot be determined. -/
  | dep
  /-- A determiner (article, demonstrative, etc.) in a nominal. -/
  | det
  /-- An interjection, filler or non-adverbial discourse marker. -/
  | discourse
  /-- A peripheral nominal, such as a topic or afterthought, that fills no regular role of the
  predicate. -/
  | dislocated
  /-- A pronominal form in a core argument position that is assigned no semantic role. -/
  | expl
  /-- An element of a grammaticalized fixed expression that behaves as a function word or short
  adverbial. -/
  | fixed
  /-- An element of a headless semi-fixed multiword expression, such as a name. -/
  | flat
  /-- A part of a word that is separated from the rest but goes with it by orthography or
  wordhood. -/
  | goeswith
  /-- A nominal core argument of a verb that is neither its subject nor its object. -/
  | iobj
  /-- An element of a sequence of comparable items interpreted as a list. -/
  | list
  /-- A function word marking a clause as subordinate. -/
  | mark
  /-- A nominal modifying another nominal. -/
  | nmod
  /-- The nominal core argument that is the syntactic subject, or pivot, of a predicate. -/
  | nsubj
  /-- A numeral in a nominal. -/
  | nummod
  /-- The most basic nominal core argument that is not the subject. -/
  | obj
  /-- A nominal functioning as a non-core modifier of a predicate. -/
  | obl
  /-- An orphaned dependent of an elided predicate. -/
  | orphan
  /-- A constituent placed beside another with no explicit coordination or subordination. -/
  | parataxis
  /-- Punctuation, attached to the head of its clause or phrase. -/
  | punct
  /-- The repair of a disfluency, normally in speech. -/
  | reparandum
  /-- The root of the sentence. -/
  | root
  /-- A nominal directed to an addressee. -/
  | vocative
  /-- A clausal complement of a verb or adjective with an obligatorily controlled subject. -/
  | xcomp
  deriving DecidableEq, Fintype, Repr

namespace DepRel

/-- There are 37 universal relations. -/
theorem card : Fintype.card DepRel = 37 := rfl

/-- The functional categories of the typology, which classify a dependent by its relation to its
head. -/
inductive FunctionalCategory where
  /-- A core argument of a clausal predicate. -/
  | core
  /-- A non-core dependent of a clausal predicate. -/
  | nonCore
  /-- A dependent of a nominal. -/
  | nominalDependent
  deriving DecidableEq, Fintype, Repr

/-- The structural categories of the typology, which classify a dependent by its form. -/
inductive StructuralCategory where
  | nominal
  | clause
  | modifierWord
  | functionWord
  deriving DecidableEq, Fintype, Repr

/-- A place in the typology, either a cell of the main table or one of the five groups of
relations that are not dependency relations in the narrow sense. -/
inductive Kind where
  /-- The cell of a functional and a structural category. -/
  | cell (f : FunctionalCategory) (s : StructuralCategory)
  /-- The relations of coordination. -/
  | coordination
  /-- The relations of multiword expressions. -/
  | multiwordExpression
  /-- The relations of loose joining, lists and parataxis. -/
  | loose
  /-- The relations of ellipsis, split words and disfluencies. -/
  | special
  /-- Punctuation, the root and the unspecified dependency. -/
  | other
  deriving DecidableEq, Repr

/-- The place of a relation in the typology. -/
def kind : DepRel → Kind
  | nsubj | obj | iobj => .cell .core .nominal
  | csubj | ccomp | xcomp => .cell .core .clause
  | obl | vocative | expl | dislocated => .cell .nonCore .nominal
  | advcl => .cell .nonCore .clause
  | advmod | discourse => .cell .nonCore .modifierWord
  | aux | cop | mark => .cell .nonCore .functionWord
  | nmod | appos | nummod => .cell .nominalDependent .nominal
  | acl => .cell .nominalDependent .clause
  | amod => .cell .nominalDependent .modifierWord
  | det | clf | case_ => .cell .nominalDependent .functionWord
  | conj | cc => .coordination
  | fixed | flat | compound => .multiwordExpression
  | list | parataxis => .loose
  | orphan | goeswith | reparandum => .special
  | punct | root | dep => .other

/-- A relation of the core arguments of a clausal predicate, nominal or clausal. -/
def IsCore (r : DepRel) : Prop := ∃ s, r.kind = .cell .core s

instance : DecidablePred IsCore := fun _ ↦ inferInstanceAs (Decidable (∃ _, _))

end DepRel

end UD
