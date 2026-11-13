/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.UD.UPOS
public import Linglib.Morphology.ConstructionMorphology.Pattern
public import Linglib.Morphology.Morph
public import Linglib.Morphology.Root.Basic
public import Linglib.Morphology.Root.Consonantal
public import Linglib.Morphology.Word.Comparative
public import Studies.Bloomfield1933

/-!
# Haspelmath (2025): Roots and root classes in comparative grammar

Haspelmath defines a root as a contentful form that can occur in a free form with no other
contentful form, the `Morphology.Comparative.Inventory.IsRoot` of a language's free forms. The
qualifying clause excludes contentful affixes such as the Japanese causative *-ase*, combining
forms such as *geo-* and free forms without a lexical meaning such as *hello*, all of them
morphological cores in the formal sense of `Morphology.IsCore`, and it admits bound roots such as
Sorbian *žon-*. Roots are concrete forms, so [the four Arabic forms sharing k-t-b are four
roots](##Haspelmath2025b.arabic_four_roots), and on the heterosemy view [the noun and the verb
*hammer* are two roots with one shape](##Haspelmath2025b.hammer_two_roots), [related by sister
schemas](##Haspelmath2025b.hammer_sisters) that *hammer* and *dance* do not instantiate. In
Bloomfield's English words [the roots are the stems](##Haspelmath2025b.bloomfield_roots),
the suppletive *bet-* of *bet-ter* but not its *-er*.

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

* [bloomfield-1933]
* [haspelmath-2023]
* [haspelmath-2025b]
* [jackendoff-audring-2020]
-/

@[expose] public section

namespace Haspelmath2025b

open Morphology Morphology.Comparative

/-! ### Root classes (§5) -/

/-- The word classes of (10) are comparative concepts, a verb being an action-denoting root, a
noun an object-denoting root and an adjective a property-denoting root. -/
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

/-- The inventory of free forms whose roots are classed by their meanings. -/
def inventory (forms : List (List Form)) : Inventory Form := ⟨forms, Form.meaning⟩

/-- A stem is a contiguous string of at least one root and possibly some affixes that can be
combined with an affix (fn. 6). -/
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

-- §2
theorem ase_not_root : japanese.IsContentful ase ∧ ¬ japanese.IsRoot ase ∧
    japanese.IsRoot yom ∧ IsCore japanese.forms ase := by
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

-- §2
theorem geo_not_root : ¬ english.IsRoot geo ∧ IsCore english.forms geo := by
  decide

-- fn. 10
theorem hello_not_root : ¬ english.IsRoot hello ∧ IsCore english.forms hello := by
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

-- §3, fn. 2
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

-- §4
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

/-! ### Suppletive alternants -/

/-- Bloomfield's plain and derived words, with the class of each morph's meaning. -/
def bloomfield : Inventory Morph where
  forms := [Bloomfield1933.Lexeme.kind, .good, .ox, .card, .go, .land].flatMap fun l ↦
    [Bloomfield1933.word l .plain, Bloomfield1933.word l l.derived]
  rootClass m :=
    if m = Bloomfield1933.kind ∨ m = Bloomfield1933.good ∨ m = Bloomfield1933.bet then
      some .property
    else if m = Bloomfield1933.ox ∨ m = Bloomfield1933.card then some .object
    else if m = Bloomfield1933.go ∨ m = Bloomfield1933.went ∨ m = Bloomfield1933.land then
      some .action
    else none

/-- In each of Bloomfield's words the roots of definition (1) are its stem, the exponent Vocabulary
Insertion gives the root, *bet-* in *bet-ter* and *went* among them, so the clause on contentful
forms tells a suppletive alternant of a root from the affix beside it. -/
theorem bloomfield_roots : ∀ l, ∀ c ∈ [.plain, l.derived],
    (Bloomfield1933.word l c).filter bloomfield.IsRoot ∈
      Bloomfield1933.english.stem.realize l c := by
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
  deriving DecidableEq, Inhabited, Repr

/-- (21): The sister schemas `X (noun)` and `X (verb)` are one pattern over the tiers of both.
The categories are constants, the two meanings are variables, and the shape `Y` is one
variable of both schemas (index 2). -/
abbrev nounVerb : ConstructionMorphology.Pattern (Tier ⊕ Tier) (Flat Value) :=
  .ofTerms (X := Fin 3) (Sum.elim
    (fun | .semantics => .inr 0 | .morphosyntax => .inl (.category .object) | .phonology => .inr 2)
    (fun | .semantics => .inr 1 | .morphosyntax => .inl (.category .action) | .phonology => .inr 2))

/-- `hammerNoun` is the noun `hammer` of (20a). -/
def hammerNoun : Tier → Value
  | .semantics => .meaning "HAMMER"
  | .morphosyntax => .category .object
  | .phonology => .shape "hæmər"

/-- `hammerVerb` is the verb `hammer` of (20b). -/
def hammerVerb : Tier → Value
  | .semantics => .meaning "HIT (WITH SOMETHING LIKE HAMMER)"
  | .morphosyntax => .category .action
  | .phonology => .shape "hæmər"

/-- `dance` (verb), whose shape differs from `hammer`'s. -/
def danceVerb : Tier → Value
  | .semantics => .meaning "DANCE"
  | .morphosyntax => .category .action
  | .phonology => .shape "dæns"

open ConstructionMorphology.Pattern in
/-- The two *hammer* roots of (20) instantiate the sister schemas of (21) as a pair, neither derived
from the other. -/
theorem hammer_sisters :
    nounVerb ≤ ofItem (Sum.elim (Flat.some ∘ hammerNoun) (Flat.some ∘ hammerVerb)) := by
  decide

open ConstructionMorphology.Pattern in
theorem hammer_dance_not_sisters :
    ¬ nounVerb ≤ ofItem (Sum.elim (Flat.some ∘ hammerNoun) (Flat.some ∘ danceVerb)) := by
  decide

end Haspelmath2025b
