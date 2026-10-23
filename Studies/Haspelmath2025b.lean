module

public import Mathlib.Order.WithBot
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.UD.UPOS
public import Linglib.Morphology.ConstructionMorphology.Schema
public import Linglib.Morphology.Root.Basic
public import Linglib.Morphology.Root.Consonantal
public import Linglib.Morphology.Word.Comparative

/-!
# Haspelmath (2025): Roots and root classes in comparative grammar

This file formalizes the definition of the root as a comparative concept in Haspelmath's chapter.
Its definition (1), a contentful form (`Form`, a morph with its meaning class) that occurs in a
free form with no other contentful form, is the root of `Morphology.Comparative`, read over a
fragment's free-form inventory. The qualifying clause separates roots from contentful affixes
(the Japanese causative `-ase`) and neoclassical combining forms (`geo-`), which are
morphological cores under the formal base definition of `Morphology/Root/Basic.lean` but not
roots; it admits bound roots (Sorbian `žon-`) and excludes free forms without a lexical meaning
(`hello`, fn. 10). Roots are concrete forms (§4), so the four Arabic forms sharing the skeleton
k-t-b are four roots (`arabic_four_roots`) and the German ablaut pair `lauf` ~ `lief` two.
`upos` is (10), word classes as comparative concepts, and `unmarkedFunction` the prototypical
combinations of (9).

§6 adopts the heterosemy view: `hammer` (noun) and `hammer` (verb) are two roots with one
shape (`hammer_two_roots`), related by the sister schemas of (21) (`nounVerb`, one
description over shared variables read through two subscriptings,
`ConstructionMorphology.Schema.InstantiatesAt`), which the pair instantiates
(`hammer_sisters`) and
`hammer`/`dance` does not.

## Implementation notes

* `Form` pairs a substrate `Morph`, the shape side, with an `Option RootClass` standing in
  for its meaning, which is all definition (1) and the lexical meaning of (11) need.
  Relatedness of meaning within a heterosemous root set is carried by the schema of (21),
  not by the forms.
* `IsStemIn` is the stem definition of fn. 6, with the Latin `laud-ab-` case; its affixes are
  those of `Morphology.Comparative.Inventory.IsAffix` over the roots of definition (1).
* The chapter names the combining forms *geo-* and *socio-* in prose only; the English word
  *geology*, with its *-logy*, is this file's illustration of *geo-*.

## References

* [haspelmath-2023]
* [haspelmath-2025b]
* [jackendoff-audring-2020]
-/

@[expose] public section

namespace Haspelmath2025b

open Morphology Morphology.Comparative

/-! ### Root classes (§5) -/

/-- Word classes are comparative concepts (10): a verb is an action-denoting root, a noun
an object-denoting root, an adjective a property-denoting root. -/
def upos : RootClass → UD.UPOS
  | .action => .VERB
  | .object => .NOUN
  | .property => .ADJ

/-- The discourse functions of (9). -/
inductive DiscourseFunction where
  | predication
  | reference
  | modification
  deriving DecidableEq, Fintype, Repr

/-- `unmarkedFunction c` is the discourse function in which the class `c` needs no function
indicator (9): no
copula or verbalizer for action roots in predication, no nominalizer for object roots in
reference, no relativizer or genitive for property roots in modification. -/
def unmarkedFunction : RootClass → DiscourseFunction
  | .action => .predication
  | .object => .reference
  | .property => .modification

/-! ### Definition (1) -/

/-- A form (§2, §4) is a morph, the pairing of a shape with a meaning, recorded with its root
class when it denotes an action, an object or a property and `none` otherwise. -/
structure Form where
  /-- The morph. -/
  shape : Morph
  /-- The root class the form denotes, if any. -/
  meaning : Option RootClass
  deriving DecidableEq, Repr

/-- The shapes of the forms of a word, for the formal definitions of
`Morphology/Root/Basic.lean`. -/
def shapes (w : List Form) : List Morph := w.map Form.shape

/-- The inventory of free forms whose roots are classed by their meanings. -/
def inventory (forms : List (List Form)) : Inventory Form := ⟨forms, Form.meaning⟩

/-- Fn. 6: a stem is a contiguous string of at least one root and possibly some affixes that
can be combined with an affix. -/
def IsStemIn (words : List (List Form)) (L : Inventory Form) (s : List Form) : Prop :=
  let root := L.IsRoot
  let affix := L.IsAffix root
  (∃ f ∈ s, root f) ∧ (∀ f ∈ s, root f ∨ affix f) ∧
    ∃ w ∈ words, ∃ a ∈ w, affix a ∧ (w = s ++ [a] ∨ w = a :: s)

instance (words : List (List Form)) (L : Inventory Form) (s : List Form) :
    Decidable (IsStemIn words L s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∃ w ∈ words, ∃ a ∈ w, _))

/-! ### Contentful affixes and combining forms (§2) -/

/-- The Japanese action root `yom` 'read'. -/
def yom : Form := ⟨.root "yom", some .action⟩
/-- The Japanese causative suffix `-ase`, which denotes an action. -/
def ase : Form := ⟨.suff "ase", some .action⟩
/-- The Japanese nonpast suffix `-u`. -/
def u : Form := ⟨.suff "u", none⟩
/-- The Japanese nonpast suffix `-ru`. -/
def ru : Form := ⟨.suff "ru", none⟩

/-- The Japanese free forms `yom-u` 'read' and `yom-ase-ru` 'make read'. -/
def japanese : Inventory Form := inventory [[yom, u], [yom, ase, ru]]

/-- The causative `-ase` is contentful but never occurs without another contentful form, so
it is not a root, while `yom` is (§2). -/
theorem ase_not_root : japanese.IsContentful ase ∧ ¬ japanese.IsRoot ase ∧
    japanese.IsRoot yom := by
  decide

/-- The neoclassical combining form `geo-`. -/
def geo : Form := ⟨.root "geo", some .object⟩
/-- The neoclassical combining form `-logy`. -/
def logy : Form := ⟨.root "logy", some .object⟩
/-- The English interjection `hello` (fn. 10). -/
def hello : Form := ⟨.free "hello", none⟩
/-- The English object root `hammer` (12a). -/
def hammerN : Form := ⟨.root "hammer", some .object⟩
/-- The English action root `hammer` (12b). -/
def hammerV : Form := ⟨.root "hammer", some .action⟩
/-- The English plural suffix. -/
def s : Form := ⟨.suff "s", none⟩
/-- The English past suffix. -/
def ed : Form := ⟨.suff "ed", none⟩

/-- The English free forms are `geology` (an illustration), `hello`, and the *hammer* forms. -/
def english : Inventory Form := inventory
  [[geo, logy], [hello], [hammerN], [hammerN, s], [hammerV], [hammerV, ed]]

/-- `geo-` is not a root, though it is a morphological core under the formal base definition (§2).
-/
theorem geo_not_root :
    ¬ english.IsRoot geo ∧
      geo.shape.IsCoreIn (english.forms.map shapes) (english.forms.map shapes) := by
  decide

/-- `hello` is a free form without a lexical meaning, hence not a root, although it is a
morphological core (fn. 10). -/
theorem hello_not_root :
    ¬ english.IsRoot hello ∧
      hello.shape.IsCoreIn (english.forms.map shapes) (english.forms.map shapes) := by
  decide

/-- The Sorbian object root `žon-` 'wife'. -/
def žon : Form := ⟨.root "žon", some .object⟩
/-- The Sorbian nominative suffix. -/
def a : Form := ⟨.suff "a", none⟩
/-- The Sorbian genitive suffix. -/
def y : Form := ⟨.suff "y", none⟩
/-- The Sorbian accusative suffix. -/
def uAcc : Form := ⟨.suff "u", none⟩

/-- The Sorbian free forms `žon-a`, `žon-y`, `žon-u` (§3). -/
def sorbian : Inventory Form := inventory [[žon, a], [žon, y], [žon, uAcc]]

/-- `žon-` always occurs with an inflectional affix, yet it is a root (§3, fn. 2). -/
theorem žon_bound_root : sorbian.IsRoot žon ∧ sorbian.IsBound žon := by decide

/-! ### Roots as concrete forms (§4) -/

/-- The German action root `lauf` 'run'. -/
def lauf : Form := ⟨.root "lauf", some .action⟩
/-- The German ablaut root `lief` 'ran'. -/
def lief : Form := ⟨.root "lief", some .action⟩
/-- The German first-singular suffix. -/
def e : Form := ⟨.suff "e", none⟩
/-- The German plural and participial suffix. -/
def en : Form := ⟨.suff "en", none⟩
/-- The German participial prefix. -/
def ge : Form := ⟨.pref "ge", none⟩

/-- The German verb forms of (5) are `lauf-e`, `lauf-en`, `lauf`, `ge-lauf-en`, `lief`. -/
def german : Inventory Form := inventory [[lauf, e], [lauf, en], [lauf], [ge, lauf, en], [lief]]

/-- With no replacive morphs, `lauf` and `lief` are two roots (§4). -/
theorem lauf_lief_roots :
    german.IsRoot lauf ∧ german.IsRoot lief ∧ lauf ≠ lief := by
  decide

/-- The consonantal skeleton of a form is its shape with the vowels removed. -/
def skeleton (f : Form) : ConsonantalRoot Char :=
  ⟨f.shape.form.toList.filter (· ∉ ['a', 'i', 'u'])⟩

/-- The Arabic action root `katab` 'wrote'. -/
def katab : Form := ⟨.root "katab", some .action⟩
/-- The Arabic action root `ktub` 'write'. -/
def ktub : Form := ⟨.root "ktub", some .action⟩
/-- The Arabic object root `kaatib` 'writer'. -/
def kaatib : Form := ⟨.root "kaatib", some .object⟩
/-- The Arabic object root `kitaab` 'book'. -/
def kitaab : Form := ⟨.root "kitaab", some .object⟩
/-- The Arabic first-plural suffix. -/
def naa : Form := ⟨.suff "naa", none⟩
/-- The Arabic first-plural prefix. -/
def na : Form := ⟨.pref "na", none⟩

/-- The Arabic forms of (6) are `katab-naa`, `na-ktub-u`, `kaatib`, `kitaab`. -/
def arabic : Inventory Form := inventory [[katab, naa], [na, ktub, u], [kaatib], [kitaab]]

/-- The forms of (6) contain four distinct roots sharing the skeleton k-t-b, which is not
itself a root (§4). -/
theorem arabic_four_roots :
    (∀ f ∈ [katab, ktub, kaatib, kitaab],
        arabic.IsRoot f ∧ skeleton f = ⟨['k', 't', 'b']⟩) ∧
      [katab, ktub, kaatib, kitaab].Nodup := by
  decide

/-- The Latin action root `laud` 'praise'. -/
def laud : Form := ⟨.root "laud", some .action⟩
/-- The Latin imperfect suffix. -/
def ab : Form := ⟨.suff "ab", none⟩
/-- The Latin first-singular imperfect suffix. -/
def am : Form := ⟨.suff "am", none⟩
/-- The Latin first-singular present suffix. -/
def o : Form := ⟨.suff "o", none⟩

/-- The Latin forms `laud-o` 'I praise' and `laud-ab-am` 'I was praising'. -/
def latin : Inventory Form := inventory [[laud, o], [laud, ab, am]]

theorem laudab_stem :
    IsStemIn latin.forms latin [laud, ab] ∧ IsStemIn latin.forms latin [laud] := by
  decide

/-! ### Heterosemy (§6) -/

/-- `hammer` (noun) and `hammer` (verb) are two roots with one shape (§6). -/
theorem hammer_two_roots :
    english.IsRoot hammerN ∧ english.IsRoot hammerV ∧
      hammerN ≠ hammerV ∧ hammerN.shape = hammerV.shape := by
  decide

/-- The tiers of the schemas of (18)–(21). -/
inductive Tier where
  | semantics
  | morphosyntax
  | phonology
  deriving DecidableEq, Fintype, Repr

/-- A tier value is a meaning, a word class, or a shape. -/
inductive Value where
  | meaning (m : String)
  | category (c : RootClass)
  | shape (s : String)
  deriving DecidableEq, Repr

/-- Tier values are discrete: a constant is dominated only by itself. -/
instance : PartialOrder Value where
  le a b := a = b
  le_refl _ := rfl
  le_trans _ _ _ h h' := h.trans h'
  le_antisymm _ _ h _ := h

instance : DecidableLE Value := λ a b => inferInstanceAs (Decidable (a = b))

/-- A tier description is a value, or `⊥` for an open variable. -/
abbrev Slot := WithBot Value

/-- The variables of the sister schemas (21) are the meaning and the category of each root, and
the shape `Y` they share (index 2). -/
inductive RootVar
  | nounMeaning
  | nounCategory
  | verbMeaning
  | verbCategory
  | shape
  deriving DecidableEq

/-- The sister schemas `X (noun)` and `X (verb)` of (21) form one description over their
variables, with the categories pinned and the meanings and the shared shape open. -/
def nounVerb : ConstructionMorphology.Schema RootVar Slot where
  body
    | .nounCategory => ↑(Value.category .object)
    | .verbCategory => ↑(Value.category .action)
    | _ => ⊥
  opens := {.nounMeaning, .verbMeaning, .shape}

/-- The subscripting of the tiers of the noun schema by the variables of (21). -/
def nounSub : Tier → RootVar
  | .semantics => .nounMeaning
  | .morphosyntax => .nounCategory
  | .phonology => .shape

/-- The subscripting of the tiers of the verb schema by the variables of (21). -/
def verbSub : Tier → RootVar
  | .semantics => .verbMeaning
  | .morphosyntax => .verbCategory
  | .phonology => .shape

/-- Schema (21a), `X (noun)`, pairs an object meaning related to `X` with a noun and the open
shape `Y`. -/
def nounSchema : ConstructionMorphology.Schema Tier Slot := nounVerb.comap nounSub

/-- Schema (21b), `X (verb)`, pairs doing in relation to `X` with a verb and the open shape
`Y`. -/
def verbSchema : ConstructionMorphology.Schema Tier Slot := nounVerb.comap verbSub

/-- `hammerNoun` is the noun `hammer` of (20a). -/
def hammerNoun : Tier → Slot
  | .semantics => ↑(Value.meaning "HAMMER")
  | .morphosyntax => ↑(Value.category .object)
  | .phonology => ↑(Value.shape "hæmər")

/-- `hammerVerb` is the verb `hammer` of (20b). -/
def hammerVerb : Tier → Slot
  | .semantics => ↑(Value.meaning "HIT (WITH SOMETHING LIKE HAMMER)")
  | .morphosyntax => ↑(Value.category .action)
  | .phonology => ↑(Value.shape "hæmər")

/-- `dance` (verb), whose shape differs from `hammer`'s. -/
def danceVerb : Tier → Slot
  | .semantics => ↑(Value.meaning "DANCE")
  | .morphosyntax => ↑(Value.category .action)
  | .phonology => ↑(Value.shape "dæns")

/-- The variables of (21) filled by the two *hammer* roots. -/
def hammerRoots : RootVar → Slot
  | .nounMeaning => hammerNoun .semantics
  | .nounCategory => hammerNoun .morphosyntax
  | .verbMeaning => hammerVerb .semantics
  | .verbCategory => hammerVerb .morphosyntax
  | .shape => hammerNoun .phonology

/-- The two *hammer* roots of (20) instantiate the sister schemas of (21) as a pair, neither derived
from the other. -/
theorem hammer_sisters :
    nounVerb.InstantiatesAt (Sum.elim nounSub verbSub) (Sum.elim hammerNoun hammerVerb) :=
  ⟨hammerRoots, λ v => by cases v <;> first | exact bot_le | exact le_rfl,
    funext λ t => by rcases t with t | t <;> cases t <;> rfl⟩

theorem hammer_dance_not_sisters :
    ¬ nounVerb.InstantiatesAt (Sum.elim nounSub verbSub) (Sum.elim hammerNoun danceVerb) :=
  λ h => by
    simpa [hammerNoun, danceVerb] using
      (ConstructionMorphology.Schema.instantiatesAt_elim_iff.1 h).2.2.2.2 .phonology .phonology rfl

end Haspelmath2025b
