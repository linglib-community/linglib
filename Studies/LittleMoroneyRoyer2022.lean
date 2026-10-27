module

public import Linglib.Semantics.Plurality.Algebra
public import Linglib.Semantics.Composition.Tree
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
`Mereology.AlgClosure` over `({·} : α → Finset α) '' dog`. The two lexicons are driven through
`PhraseStructure.Tree.interp`: the Ch'ol root is measure modification by the atom count,
`Mereology.QMOD`, and the Shan root is the partition numeral `IoninMatushansky2006.cardMod` over
the atomized noun, `Mereology.atomize`. The distributional diagnostics of the paper's §4, its case
against a uniform classifier semantics such as Chierchia's, then follow from the lexical types.

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

open Montague Mereology PhraseStructure
open IoninMatushansky2006 (cardMod cardMod_atoms_iff)

/-! ### The two strategies, in the morphology -/

/-- Ch'ol classifiers are suffixes on the numeral, as the fragment's entries record. -/
theorem chol_classifiers_suffixed :
    ∀ c ∈ Chol.Classifiers.classifiers, c.kind = .bound .after .affix := by
  decide

/-- Shan classifiers are free morphemes, as the fragment's entries record. -/
theorem shan_classifiers_free : ∀ c ∈ Shan.Classifiers.classifiers, c.kind = .free := by
  decide

variable {α : Type} [DecidableEq α] (dog : Set α) (g : Assignment (Finset α))

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

/-! ### Ch'ol: classifier-for-numeral -/

/-- *cha'* 'two' takes a measure function and then a predicate ((7)), the classifier *-kojty* is
μ# ((8)) keyed on `Chol.Classifiers.kojty`, the Spanish loan *ocho* 'eight' has its measure built
in ((34b)), and *ts'i'* is 'dog'. -/
def cholLex : Lexicon (Finset α) Unit := fun w ↦
  if w = "cha'" then some ⟨(.e ⇒ .n) ⇒ (.e ⇒ .t) ⇒ .e ⇒ .t,
    show (Finset α → ℕ) → (Finset α → Prop) → Finset α → Prop from fun m P ↦ QMOD P m 2⟩
  else if w = Chol.Classifiers.kojty.form then some ⟨.e ⇒ .n, Finset.card⟩
  else if w = "ocho" then some ⟨(.e ⇒ .t) ⇒ .e ⇒ .t,
    show (Finset α → Prop) → Finset α → Prop from fun P ↦ QMOD P Finset.card 8⟩
  else if w = "ts'i'" then some ⟨.e ⇒ .t, dogs dog⟩
  else none

/-- In *cha'-kojty*, numeral and classifier form a constituent ((23a)). -/
def cholNumClf : Tree Unit String := .bin (.leaf "cha'") (.leaf Chol.Classifiers.kojty.form)

/-- `[[cha' -kojty] ts'i']` ((51)). -/
def cholTree : Tree Unit String := .bin cholNumClf (.leaf "ts'i'")

/-- The Ch'ol root is the noun measure-modified by the atom count to two ((51)). -/
theorem cholTree_interp :
    cholTree.interp (cholLex dog) g = some ⟨.e ⇒ .t, QMOD (dogs dog) Finset.card 2⟩ :=
  rfl

/-- Numeral and classifier compose without a noun, into a measure phrase that restricts any
predicate to its pluralities of two atoms ((45)–(46), Prediction 4). -/
theorem chol_numClf_composes :
    cholNumClf.interp (cholLex dog) g =
      some ⟨(.e ⇒ .t) ⇒ .e ⇒ .t, fun P ↦ QMOD P Finset.card 2⟩ :=
  rfl

/-- The classifier, a measure of type `⟨e,n⟩`, cannot compose with the noun
without the numeral ((43a)). -/
theorem chol_clfNoun_fails :
    Tree.interp (cholLex dog) g (.bin (.leaf Chol.Classifiers.kojty.form) (.leaf "ts'i'")) = none :=
  rfl

/-- *ocho* composes with the noun directly ((33), Prediction 1). -/
theorem chol_ocho_composes :
    Tree.interp (cholLex dog) g (.bin (.leaf "ocho") (.leaf "ts'i'")) =
      some ⟨.e ⇒ .t, QMOD (dogs dog) Finset.card 8⟩ :=
  rfl

/-- *ocho* rejects the classifier ((34), Prediction 1). -/
theorem chol_ocho_clf_fails :
    Tree.interp (cholLex dog) g (.bin (.leaf "ocho") (.leaf Chol.Classifiers.kojty.form)) = none :=
  rfl

/-! ### Shan: classifier-for-noun -/

/-- *sɔ̌ŋ* 'two' is the partition numeral ((10), `IoninMatushansky2006.cardMod`),
the classifier *tǒ* atomizes ((13), `Mereology.atomize`) keyed on
`Shan.Classifiers.«to»`, and *mǎa* is 'dog'. -/
def shanLex : Lexicon (Finset α) Unit := fun w ↦
  if w = "sɔ̌ŋ" then some ⟨(.e ⇒ .t) ⇒ .e ⇒ .t, cardMod 2⟩
  else if w = Shan.Classifiers.«to».form then some ⟨(.e ⇒ .t) ⇒ .e ⇒ .t,
    show (Finset α → Prop) → Finset α → Prop from atomize⟩
  else if w = "mǎa" then some ⟨.e ⇒ .t, dogs dog⟩
  else none

/-- In *tǒ mǎa*, classifier and noun form a constituent ((23b)). -/
def shanClfNoun : Tree Unit String := .bin (.leaf Shan.Classifiers.«to».form) (.leaf "mǎa")

/-- `[sɔ̌ŋ [tǒ mǎa]]` ((52)), abstracting from the surface order *mǎa sɔ̌ŋ tǒ*
((25)) as the paper does. -/
def shanTree : Tree Unit String := .bin (.leaf "sɔ̌ŋ") shanClfNoun

/-- The Shan root is the partition numeral over the atomized noun ((52)). -/
theorem shanTree_interp :
    shanTree.interp (shanLex dog) g = some ⟨.e ⇒ .t, cardMod 2 (atomize (dogs dog))⟩ :=
  rfl

/-- Classifier and noun compose without a numeral, yielding the atoms
((42), Prediction 3). -/
theorem shan_clfNoun_composes :
    shanClfNoun.interp (shanLex dog) g = some ⟨.e ⇒ .t, atomize (dogs dog)⟩ :=
  rfl

/-- Numeral and classifier, both `⟨⟨e,t⟩,⟨e,t⟩⟩`, do not compose without the
noun ((48)–(49)). -/
theorem shan_numClf_fails :
    Tree.interp (shanLex dog) g (.bin (.leaf "sɔ̌ŋ") (.leaf Shan.Classifiers.«to».form)) = none :=
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
