module

public import Linglib.Semantics.Plurality.Algebra
public import Linglib.Semantics.Composition.Constituency
public import Linglib.Semantics.Composition.Rules
public import Linglib.Semantics.Composition.Sorts
public import Studies.Borer2005
public import Studies.IoninMatushansky2006
public import Linglib.Fragments.Mayan.Chol.Classifiers
public import Linglib.Fragments.Shan.Classifiers
public import Linglib.Semantics.Mereology.Extensive

/-!
# Little, Moroney and Royer (2022): Classifiers Can Be for Numerals or Nouns

Little, Moroney and Royer distinguish two strategies of numeral modification. In a
classifier-for-numeral language the classifier is the measure function the numeral demands; in a
classifier-for-noun language it atomizes the noun so that a partition numeral can count. Ch'ol
takes the first path and Shan the second, with constituency `[[Num Clf] N]` against
`[Num [Clf N]]`, and the two derivations reach the same denotation.

A count noun denotes Link's star of its atoms, the singletons of its individuals, so the noun is
mathlib's `supClosure` of `({·} : α → Finset α) '' dog`. Both derivations are by Functional
Application alone: the Ch'ol root is measure modification by the atom count, and the Shan root
is the partition numeral `IoninMatushansky2006.cardMod` over the atomized noun,
`Mereology.atomize`. The distributional diagnostics of the paper's §4, its case against a uniform
classifier semantics such as Chierchia's, then follow from the lexical types.

## Implementation notes

Pluralities are `Finset α`, so μ# is `Finset.card` at type `⟨e,n⟩`, and its strict monotonicity
is all that quantization needs (`qua_dogs_card_eq`). The strategies part at zero, where the
partition numeral holds of the empty sum that the noun excludes. Prediction 2 of §4, nouns that
need no classifier, rests on Vietnamese rather than Ch'ol or Shan data and is not formalized. The
remark on plural marking is stated over the range assignment of `Studies/Borer2005.lean`: a
classifier that is a head of the nominal spine assigns range to Borer's dividing value, as plural
inflection does, and a classifier inside the numeral's phrase assigns none. The Mi'gmaq examples
of that section are not recorded.

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
def dogs : Finset α → Prop := (· ∈ supClosure (({·} : α → Finset α) '' dog))

theorem dogs_iff (x : Finset α) : dogs dog x ↔ x.Nonempty ∧ ↑x ⊆ dog :=
  mem_supClosure_image_singleton dog x

/-- Atomizing a count noun yields its atoms ((13)), the singletons of its individuals. -/
theorem atomize_dogs : atomize {x | dogs dog x} = ({·} : α → Finset α) '' dog :=
  atomize_mem_supClosure fun _ ⟨a, _, h⟩ ↦ h ▸ (Finset.isAtom_singleton a)

theorem dogs_and_card_eq_iff {n : ℕ} (hn : n ≠ 0) (x : Finset α) :
    dogs dog x ∧ x.card = n ↔ x.card = n ∧ ↑x ⊆ dog := by
  simp only [dogs_iff, ← Finset.card_pos]
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
  | _, .measureNumeral => fun m P x ↦ P x ∧ m x = 2
  | _, .measure => Finset.card
  | _, .measuredNumeral => fun P x ↦ P x ∧ x.card = 8
  | _, .partitionNumeral => cardMod 2
  | _, .atomizer => fun P ↦ (· ∈ atomize {x | P x})
  | _, .noun => dogs dog

/-- The denotations of a tree, by Functional Application. -/
def meanings (t : Tree Unit Word) : List (Σ a : Ty Base, a.Dom (Base.Dom (Finset α) Unit)) :=
  t.values (typeDriven application) inferInstance (Item.val dog) items

/-! ### Ch'ol: classifier-for-numeral -/

/-- In *cha'-kojty*, numeral and classifier form a constituent ((23a)). -/
def cholNumClf : Tree Unit Word := .bin (.leaf .cha) (.leaf (.cholClf Chol.Classifiers.kojty))

/-- `[[cha' -kojty] ts'i']` ((51)). -/
def cholTree : Tree Unit Word := .bin cholNumClf (.leaf .tsi)

/-- The Ch'ol root is the noun measure-modified by the atom count to two ((51)). -/
theorem meanings_cholTree :
    meanings dog cholTree = [⟨.et, fun x ↦ dogs dog x ∧ x.card = 2⟩] :=
  rfl

/-- Numeral and classifier compose without a noun, into a measure phrase that restricts any
predicate to its pluralities of two atoms ((45)–(46), Prediction 4). -/
theorem meanings_cholNumClf :
    meanings dog cholNumClf = [⟨.et ⇒ .et, fun P x ↦ P x ∧ x.card = 2⟩] :=
  rfl

/-- The classifier, a measure of type `⟨e,n⟩`, cannot compose with the noun
without the numeral ((43a)). -/
theorem meanings_cholClfNoun :
    meanings dog (.bin (.leaf (.cholClf Chol.Classifiers.kojty)) (.leaf .tsi)) = [] :=
  rfl

/-- *ocho* composes with the noun directly ((33), Prediction 1). -/
theorem meanings_ocho :
    meanings dog (.bin (.leaf .ocho) (.leaf .tsi)) = [⟨.et, fun x ↦ dogs dog x ∧ x.card = 8⟩] :=
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
    meanings dog shanTree = [⟨.et, cardMod 2 (· ∈ atomize {x | dogs dog x})⟩] :=
  rfl

/-- Classifier and noun compose without a numeral, yielding the atoms
((42), Prediction 3). -/
theorem meanings_shanClfNoun :
    meanings dog shanClfNoun = [⟨.et, (· ∈ atomize {x | dogs dog x})⟩] :=
  rfl

/-- Numeral and classifier, both `⟨⟨e,t⟩,⟨e,t⟩⟩`, do not compose without the
noun ((48)–(49)). -/
theorem meanings_shanNumClf :
    meanings dog (.bin (.leaf .song) (.leaf (.shanClf Shan.Classifiers.«to»))) = [] :=
  rfl

/-! ### Plural marking, §3.4

For [borer-2005] a classifier and plural inflection both assign range to the dividing value of
the nominal spine, and so exclude each other. That holds of a classifier for the noun, a head of
the spine, and not of a classifier for the numeral, which sits inside the numeral's phrase. -/

open Borer2005 (Assigner WellFormed)

/-- The range a dependent of the nominal spine assigns under Borer's analysis: a classifier head
divides, a numeral counts, and a numeral with its classifier counts as the numeral does. -/
def assigner : Tree Unit Word → Option Assigner
  | .leaf (.cholClf _) | .leaf (.shanClf _) => some ⟨{.Q}, .unspecified⟩
  | .leaf .cha | .leaf .song | .bin (.leaf .cha) (.leaf (.cholClf _)) => some (.pure (.cardinal 2))
  | .leaf .ocho => some (.pure (.cardinal 8))
  | _ => none

/-- The range assigners of a nominal, from the noun up: at each node the left daughter is a
dependent of the spine and the right daughter continues it. -/
def spine : Tree Unit Word → List Assigner
  | .bin d t => spine t ++ (assigner d).toList
  | _ => []

-- A classifier for the noun divides, and is in complementary distribution with plural inflection.
theorem wellFormed_spine_shanTree :
    WellFormed (spine shanTree) ∧ ¬ WellFormed (.div :: spine shanTree) := by
  decide

/-- (30): a classifier for the numeral co-occurs with plural inflection, as in *cha'-tyikil
wiñik-ob* 'two men'. -/
theorem wellFormed_div_spine_cholTree : WellFormed (.div :: spine cholTree) := by decide

-- The structure (23b) for Ch'ol would exclude the plural of (30).
theorem not_wellFormed_div_spine_chol_23b :
    ¬ WellFormed (.div :: spine
      (.bin (.leaf .cha) (.bin (.leaf (.cholClf Chol.Classifiers.kojty)) (.leaf .tsi)))) := by
  decide

-- Without the plural, which is optional, nothing assigns range to the dividing value in (23a):
-- Borer's stems are stuff until divided, where the count noun of (6) comes with its atoms.
theorem not_wellFormed_spine_cholTree : ¬ WellFormed (spine cholTree) := by decide

/-! ### One denotation for *two dogs* -/

theorem qua_dogs_card_eq (n : ℕ) : QUA {x | dogs dog x ∧ x.card = n} :=
  qua_inter_preimage_of_strictMonoOn (Finset.card_strictMono.strictMonoOn {x | dogs dog x}) n

/-- Derivationally distinct, the two strategies denote the same pluralities for every nonzero
numeral (§4.5). -/
theorem dogs_and_card_eq_iff_cardMod_atomize {n : ℕ} (hn : n ≠ 0) (x : Finset α) :
    dogs dog x ∧ x.card = n ↔ cardMod n (· ∈ atomize {x | dogs dog x}) x := by
  rw [dogs_and_card_eq_iff dog hn, atomize_dogs, cardMod_atoms_iff]

/-- Three dogs and a cat, the model of (6) with a cat added for the noun to exclude. -/
inductive Animal | a | b | c | cat
  deriving DecidableEq, Fintype

-- *mǎa* atomized denotes the three dogs `{a, b, c}` ((52)).
example (x : Finset Animal) :
    x ∈ atomize {x | dogs {.cat}ᶜ x} ↔ x ∈ ({{.a}, {.b}, {.c}} : Finset (Finset Animal)) := by
  simp only [atomize_dogs, Set.mem_image, Set.mem_compl_singleton_iff]
  revert x
  decide

-- *two dogs* denotes `{ab, ac, bc}` ((51)–(52)).
example (x : Finset Animal) :
    dogs {.cat}ᶜ x ∧ x.card = 2 ↔
      x ∈ ({{.a, .b}, {.a, .c}, {.b, .c}} : Finset (Finset Animal)) := by
  simp only [dogs_and_card_eq_iff _ two_ne_zero, Set.subset_compl_singleton_iff, Finset.mem_coe]
  revert x
  decide

end LittleMoroneyRoyer2022
