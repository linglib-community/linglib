module

public import Linglib.Semantics.Plurality.Algebra
public import Linglib.Semantics.Composition.Interpreter.Constituency
public import Linglib.Semantics.Composition.Interpreter.Rules
public import Linglib.Semantics.Composition.Interpreter.Sorts
public import Studies.IoninMatushansky2006
public import Linglib.Fragments.Mayan.Chol.Classifiers
public import Linglib.Fragments.Shan.Classifiers

/-!
# Little, Moroney and Royer (2022): Classifiers Can Be for Numerals or Nouns

Little, Moroney and Royer distinguish two strategies of numeral modification. In a
classifier-for-numeral language the classifier is the measure function the numeral demands; in a
classifier-for-noun language it atomizes the noun so that a partition numeral can count. Ch'ol
takes the first path and Shan the second, with constituency `[[Num Clf] N]` against
`[Num [Clf N]]`, and the two derivations reach the same denotation.

A count noun denotes Link's star of its atoms, the singletons of its individuals, so the noun is
`Mereology.AlgClosure` over `({·} : α → Finset α) '' dog`. Both derivations are by Functional
Application alone: the Ch'ol root is measure modification by the atom count, `Mereology.QMOD`, and
the Shan root is the partition numeral `IoninMatushansky2006.cardMod` over the atomized noun,
`Mereology.atomize`. The distributional diagnostics of the paper's §4, its case against a uniform
classifier semantics such as Chierchia's, then follow from the lexical types.

## Implementation notes

Pluralities are `Finset α`, so μ# is `Finset.card` at type `⟨e,n⟩`, and its strict monotonicity
is all that quantization needs (`qmod_dogs_qua`). The strategies part at zero, where the partition
numeral holds of the empty sum that the noun excludes. Prediction 2 of §4, nouns that need no
classifier, rests on Vietnamese rather than Ch'ol or Shan data and is not formalized, nor is the
paper's remark on plural marking: Ch'ol classifiers co-occur with the plural, against Borer's
complementarity, which the paper keeps for classifier-for-noun languages such as Shan.

## References

* [little-moroney-royer-2022]
* [ionin-matushansky-2006]
* [chierchia-1998]
* [bale-coon-2014]
* [borer-2005]
* [krifka-1995b]
* [link-1983]
-/

@[expose] public section

namespace LittleMoroneyRoyer2022

open Interpreter Mereology PhraseStructure
open IoninMatushansky2006 (cardMod cardMod_atoms_iff)

/-! ### The two strategies, in the morphology -/

/-- Ch'ol classifiers are suffixes on the numeral, as the fragment's entries record. -/
theorem chol_classifiers_suffixed :
    ∀ c ∈ Chol.Classifiers.classifiers, c.kind = .bound .after .affix := by
  decide

/-- Shan classifiers are free morphemes, as the fragment's entries record. -/
theorem shan_classifiers_free : ∀ c ∈ Shan.Classifiers.classifiers, c.kind = .free := by
  decide

variable {α : Type} [DecidableEq α] (dog : Set α)

/-! ### Count nouns, measured and atomized -/

/-- A count noun denotes the atoms and their sums ((6)), Link's star of the singletons of its
individuals (fn. 4). -/
def dogs : Finset α → Prop := AlgClosure (· ∈ ({·} : α → Finset α) '' dog)

theorem dogs_iff (x : Finset α) : dogs dog x ↔ x.Nonempty ∧ ↑x ⊆ dog :=
  algClosure_image_singleton dog x

/-- Atomizing a count noun yields its atoms ((13)), the singletons of its individuals. -/
theorem atomize_dogs : atomize (dogs dog) = (· ∈ ({·} : α → Finset α) '' dog) :=
  atomize_algClosure fun _ ⟨a, _, h⟩ ↦ h ▸ atom_iff_isAtom.2 (Finset.isAtom_singleton a)

theorem qmod_dogs_iff {n : ℕ} (hn : n ≠ 0) (x : Finset α) :
    QMOD (dogs dog) Finset.card n x ↔ x.card = n ∧ ↑x ⊆ dog := by
  simp only [QMOD, dogs_iff, ← Finset.card_pos]
  grind

/-! ### The lexicon -/

/-- The words: the Ch'ol numerals *cha'* 'two' and *ocho* 'eight', a Ch'ol classifier and *ts'i'*
'dog'; the Shan numeral *sɔ̌ŋ* 'two', a Shan classifier and *mǎa* 'dog'. -/
inductive Word
  | cha
  | ocho
  | cholClf (c : Classifier)
  | tsi
  | song
  | shanClf (c : Classifier)
  | maa

/-- The lexical items by type. A classifier-for-numeral numeral (7) takes a measure function and
then a predicate, and its classifier (8) is a measure function; a numeral with its measure built
in (34b), a partition numeral (10) and an atomizing classifier (13) are functions on
predicates. -/
inductive Item : Ty Base → Type
  | measureNumeral : Item ((.e ⇒ .n) ⇒ .et ⇒ .et)
  | measure : Item (.e ⇒ .n)
  | measuredNumeral : Item (.et ⇒ .et)
  | partitionNumeral : Item (.et ⇒ .et)
  | atomizer : Item (.et ⇒ .et)
  | noun : Item .et

/-- The item of a word. -/
def items : Word ⊕ ℕ → List (Σ a, Item a)
  | .inl .cha => [⟨_, .measureNumeral⟩]
  | .inl .ocho => [⟨_, .measuredNumeral⟩]
  | .inl (.cholClf _) => [⟨_, .measure⟩]
  | .inl .tsi | .inl .maa => [⟨_, .noun⟩]
  | .inl .song => [⟨_, .partitionNumeral⟩]
  | .inl (.shanClf _) => [⟨_, .atomizer⟩]
  | .inr _ => []

/-- The denotations over pluralities of `α`: *cha'* is measure modification to two ((7)), a
Ch'ol classifier μ# ((8)), *ocho* measure modification by μ# to eight ((34b)), *sɔ̌ŋ* the
partition numeral ((10), `IoninMatushansky2006.cardMod`), a Shan classifier atomization ((13),
`Mereology.atomize`), and the nouns 'dog'. -/
def Item.val : {a : Ty Base} → Item a → a.Dom (Base.Dom (Finset α) Unit)
  | _, .measureNumeral => fun m P ↦ QMOD P m 2
  | _, .measure => Finset.card
  | _, .measuredNumeral => fun P ↦ QMOD P Finset.card 8
  | _, .partitionNumeral => cardMod 2
  | _, .atomizer => atomize
  | _, .noun => dogs dog

/-- The denotations of a tree, by Functional Application. -/
def meanings (t : Tree Unit Word) : List (Σ a : Ty Base, a.Dom (Base.Dom (Finset α) Unit)) :=
  t.values (typeDriven .application) inferInstance (Item.val dog) items

/-! ### Ch'ol: classifier-for-numeral -/

/-- In *cha'-kojty*, numeral and classifier form a constituent ((23a)). -/
def cholNumClf : Tree Unit Word := .bin (.leaf .cha) (.leaf (.cholClf Chol.Classifiers.kojty))

/-- `[[cha' -kojty] ts'i']` ((51)). -/
def cholTree : Tree Unit Word := .bin cholNumClf (.leaf .tsi)

/-- The Ch'ol root is the noun measure-modified by the atom count to two ((51)). -/
theorem meanings_cholTree :
    meanings dog cholTree = [⟨.et, QMOD (dogs dog) Finset.card 2⟩] :=
  rfl

/-- Numeral and classifier compose without a noun, into a measure phrase that restricts any
predicate to its pluralities of two atoms ((45)–(46), Prediction 4). -/
theorem meanings_cholNumClf :
    meanings dog cholNumClf = [⟨.et ⇒ .et, fun P ↦ QMOD P Finset.card 2⟩] :=
  rfl

/-- The classifier, a measure of type `⟨e,n⟩`, cannot compose with the noun
without the numeral ((43a)). -/
theorem meanings_cholClfNoun :
    meanings dog (.bin (.leaf (.cholClf Chol.Classifiers.kojty)) (.leaf .tsi)) = [] :=
  rfl

/-- *ocho* composes with the noun directly ((33), Prediction 1). -/
theorem meanings_ocho :
    meanings dog (.bin (.leaf .ocho) (.leaf .tsi)) = [⟨.et, QMOD (dogs dog) Finset.card 8⟩] :=
  rfl

/-- *ocho* rejects the classifier ((34), Prediction 1). -/
theorem meanings_ocho_clf :
    meanings dog (.bin (.leaf .ocho) (.leaf (.cholClf Chol.Classifiers.kojty))) = [] :=
  rfl

/-! ### Shan: classifier-for-noun -/

/-- In *tǒ mǎa*, classifier and noun form a constituent ((23b)). -/
def shanClfNoun : Tree Unit Word := .bin (.leaf (.shanClf Shan.Classifiers.«to»)) (.leaf .maa)

/-- `[sɔ̌ŋ [tǒ mǎa]]` ((52)), abstracting from the surface order *mǎa sɔ̌ŋ tǒ*
((25)) as the paper does. -/
def shanTree : Tree Unit Word := .bin (.leaf .song) shanClfNoun

/-- The Shan root is the partition numeral over the atomized noun ((52)). -/
theorem meanings_shanTree :
    meanings dog shanTree = [⟨.et, cardMod 2 (atomize (dogs dog))⟩] :=
  rfl

/-- Classifier and noun compose without a numeral, yielding the atoms
((42), Prediction 3). -/
theorem meanings_shanClfNoun :
    meanings dog shanClfNoun = [⟨.et, atomize (dogs dog)⟩] :=
  rfl

/-- Numeral and classifier, both `⟨⟨e,t⟩,⟨e,t⟩⟩`, do not compose without the
noun ((48)–(49)). -/
theorem meanings_shanNumClf :
    meanings dog (.bin (.leaf .song) (.leaf (.shanClf Shan.Classifiers.«to»))) = [] :=
  rfl

/-! ### One denotation for *two dogs* -/

theorem qmod_dogs_qua (n : ℕ) : QUA (QMOD (dogs dog) Finset.card n) :=
  qmod_qua (Finset.card_strictMono.strictMonoOn _) n

/-- Derivationally distinct, the two strategies denote the same pluralities for every nonzero
numeral (§4.5). -/
theorem qmod_iff_cardMod_atomize {n : ℕ} (hn : n ≠ 0) (x : Finset α) :
    QMOD (dogs dog) Finset.card n x ↔ cardMod n (atomize (dogs dog)) x := by
  rw [qmod_dogs_iff dog hn, atomize_dogs, cardMod_atoms_iff]

/-- Three dogs and a cat, the model of (6) with a cat added for the noun to exclude. -/
inductive Animal | a | b | c | cat
  deriving DecidableEq, Fintype

-- *mǎa* atomized denotes the three dogs `{a, b, c}` ((52)).
example (x : Finset Animal) :
    atomize (dogs {.cat}ᶜ) x ↔ x ∈ ({{.a}, {.b}, {.c}} : Finset (Finset Animal)) := by
  simp only [atomize_dogs, Set.mem_image, Set.mem_compl_singleton_iff]
  revert x
  decide

-- *two dogs* denotes `{ab, ac, bc}` ((51)–(52)).
example (x : Finset Animal) :
    QMOD (dogs {.cat}ᶜ) Finset.card 2 x ↔
      x ∈ ({{.a, .b}, {.a, .c}, {.b, .c}} : Finset (Finset Animal)) := by
  simp only [qmod_dogs_iff _ two_ne_zero, Set.subset_compl_singleton_iff, Finset.mem_coe]
  revert x
  decide

end LittleMoroneyRoyer2022
