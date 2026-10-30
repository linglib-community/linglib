module

public import Mathlib.Data.Finset.Image
public import Linglib.Semantics.Reference.Definiteness
public import Linglib.Discourse.Role
public import Linglib.Syntax.Number.Basic
public import Linglib.Morphology.Word.Basic

/-!
# Determiners

This file defines the determiner as a lexical object and the determiner inventory of a
language. The base `Determiner` carries only a surface form, and the four specializations
`Article`, `DemonstrativeDeterminer`, `QuantificationalDeterminer` and `PossessiveDeterminer` extend
it. An inventory is
a list of `Determiner.Entry` occurrences. An article marks a strength when one of the definite uses
it obligatorily expones calls for that strength, and an inventory marks the strengths its articles
mark (`Inventory.strengths`). A demonstrative marks none: whether a language's demonstrative is
obligatory in a definite use is not lexical but follows from a theory of competition between forms,
as Jenks's Index! and the Blocking Principle are. The typologies of definiteness marking, Jenks's
and Moroney's types and Patel-Grosz and Grosz's article systems, are stated in their studies, each
with its own account of when a presupposition is marked.

## Main declarations

* `Determiner` is the base record, and `Determiner.toWord` realizes it as a word.
* `Article` records definiteness, the exponent, the definite uses the article obligatorily
  expones and the number it selects; `DemonstrativeDeterminer`, `QuantificationalDeterminer` and
  `PossessiveDeterminer` are the other specializations.
* `Determiner.Entry` is an occurrence of one of the four kinds in an inventory, `Entry.kind`
  is its kind together with an article's definiteness, `Entry.strengths` the strengths it
  marks, and `Entry.Selects` the numbers of the nominals it applies to.
* `Determiner.Inventory` is a language's declared inventory, and `Inventory.strengths` the
  strengths its entries mark; `Inventory.Marks` and `Inventory.IsSyncretic` lift the entry
  predicates.
* `Determiner.Inventory.Realizes` says that the inventory carries a form for a kind of nominal
  description.
* `Article.strengths` is the set of strengths an article admits.

## Implementation notes

This file is the Frame-free lexical layer. The denotations of articles, demonstratives and
possessives are in `Semantics/Reference/Determiner.lean`, and the generalized-quantifier
denotation of a `QuantificationalDeterminer` is supplied by its consumers. `Inventory` is a `def`
rather than an `abbrev` so that its operations resolve by dot notation; its membership is the
list's, and facts about one-entry inventories go through `Inventory.marks_singleton`.
`Realizes` is
inventory data and neither licensing nor felicity. A kind can be expressed without a determiner
realizing it, as Shan anaphoric definites are by bare nouns (Moroney), and which form a context
selects is pragmatics (Jenks).

## References

* [schwarz-2009]
* [jenks-2018]
* [moroney-2021]
* [patel-grosz-grosz-2017]
-/

@[expose] public section


/-- A determiner is a D head with a surface form, a representative morpheme or a construction
label. The specializations extend it. -/
structure Determiner where
  /-- The surface form. -/
  form : String
  deriving DecidableEq, Repr

namespace Determiner

/-- A determiner is realized as a bare word of category `DET`. -/
def toWord (d : Determiner) : Morphology.Word := { form := d.form, cat := .DET }

/-- An article is exponed by a dedicated morpheme, a classifier construction, a demonstrative
form or a bare noun. Whether the form marks definiteness is a matter of the uses it expones,
not of its exponent. -/
inductive Exponent where
  /-- A dedicated article morpheme, as English *the* and German *der*. -/
  | dedicatedMorpheme
  /-- A bare classifier phrase, as the Cantonese definite [Clf-N]. -/
  | classifierPhrase
  /-- A numeral-classifier phrase, as the Cantonese indefinite [jat-Clf-N]. -/
  | numeralClassifier
  /-- A demonstrative form, as Mandarin anaphoric *na*. -/
  | demonstrativeForm
  /-- A bare noun whose reading a covert type shift fixes. -/
  | bareNoun
  deriving DecidableEq, Repr

end Determiner

/-! ### The specializations -/

/-- An article is the definite or indefinite determiner. Its `uses` are the definite uses it
obligatorily expones, and they are empty for an indefinite. -/
structure Article extends Determiner where
  /-- The article is definite or indefinite. -/
  definiteness : Definiteness
  /-- The exponent of the article. -/
  exponent : Determiner.Exponent
  /-- The definite uses the article obligatorily expones. -/
  uses : Finset DefiniteDescription.Use := ∅
  /-- The grammatical number the article selects, or none when it is number-neutral, as English
  *a* selects the singular. -/
  numberRestriction : Option Number := none
  deriving DecidableEq

/-- A demonstrative determiner carries its deictic content, the participant sets of the referents
in whose vicinity it locates its referent. -/
structure DemonstrativeDeterminer extends Determiner where
  /-- The participant sets of the referents in whose vicinity the form locates its referent. -/
  deixis : Finset (Finset Discourse.Role)
  deriving DecidableEq

/-- A quantificational determiner records only what its generalized-quantifier denotation
leaves open, the grammatical number it selects and whether it selects mass nouns, since
synonymous determiners such as *every* and *all* differ there. Everything the denotation fixes,
its force, monotonicity, strength and conservativity, is a theorem about the denotation, which
the consumers supply. -/
structure QuantificationalDeterminer extends Determiner where
  /-- The grammatical number the determiner selects, or none when it is number-neutral. -/
  numberRestriction : Option Number := none
  /-- The determiner selects mass nouns. -/
  selectsMass : Bool := false
  deriving DecidableEq, Repr

/-- A possessive determiner denotes a definite through a possession relation. -/
structure PossessiveDeterminer extends Determiner
  deriving DecidableEq, Repr

namespace Determiner

/-! ### Entries -/

/-- An entry of an inventory is an occurrence of one of the four kinds of determiner. -/
inductive Entry where
  | article (a : Article)
  | demonstrative (d : DemonstrativeDeterminer)
  | quantifier (q : QuantificationalDeterminer)
  | possessive (p : PossessiveDeterminer)
  deriving DecidableEq

namespace Entry

/-- The kind of an entry records an article's definiteness and nothing else. -/
inductive Kind where
  | article (d : Definiteness)
  | demonstrative
  | quantifier
  | possessive
  deriving DecidableEq, Repr

/-- The kind of an entry. -/
def kind : Entry → Kind
  | .article a => .article a.definiteness
  | .demonstrative _ => .demonstrative
  | .quantifier _ => .quantifier
  | .possessive _ => .possessive

/-- The definite uses an entry obligatorily expones are an article's `uses`; a demonstrative,
quantifier or possessive expones none by its lexicon. -/
def uses : Entry → Finset DefiniteDescription.Use
  | .article a => a.uses
  | .demonstrative _ | .quantifier _ | .possessive _ => ∅

/-- The grammatical number an entry selects is an article's or a quantifier's restriction; a
demonstrative or possessive selects none. -/
def numberRestriction : Entry → Option Number
  | .article a => a.numberRestriction
  | .quantifier q => q.numberRestriction
  | .demonstrative _ | .possessive _ => none

variable (e : Entry)

/-- An entry applies to a nominal of number `num` when it selects that number or none. -/
def Selects (num : Number) : Prop := ∀ n ∈ e.numberRestriction, n = num

instance (num : Number) : Decidable (e.Selects num) := by unfold Selects; infer_instance

/-- The strengths an entry marks are those its definite uses call for. -/
def strengths : Finset DefiniteDescription.Strength := e.uses.image DefiniteDescription.Use.strength

/-- An entry marks an article strength when some definite use it expones calls for it. -/
def Marks (p : DefiniteDescription.Strength) : Prop := p ∈ e.strengths

instance (p : DefiniteDescription.Strength) : Decidable (e.Marks p) :=
  inferInstanceAs (Decidable (p ∈ e.strengths))

theorem marks_iff (p : DefiniteDescription.Strength) :
    e.Marks p ↔ ∃ u ∈ e.uses, u.strength = p :=
  Finset.mem_image

/-- An entry is syncretic when it marks both strengths, as English *the* does. -/
def IsSyncretic : Prop := e.Marks .uniqueness ∧ e.Marks .familiarity

instance : Decidable e.IsSyncretic := by unfold IsSyncretic; infer_instance

end Entry

/-! ### Inventories -/

/-- A language's declared determiner inventory is a list of entries. It is a `def` so that the
operations below resolve by dot notation. -/
def Inventory := List Entry

namespace Inventory

instance : Membership Entry Inventory := inferInstanceAs (Membership Entry (List Entry))
instance : DecidableEq Inventory := inferInstanceAs (DecidableEq (List Entry))
instance (ds : Inventory) (p : Entry → Prop) [DecidablePred p] : Decidable (∃ e ∈ ds, p e) :=
  List.decidableBEx p ds

variable (ds : Inventory)

/-- The strengths an inventory marks are those its entries mark. -/
def strengths : Finset DefiniteDescription.Strength :=
  (List.map Entry.strengths ds).foldr (· ∪ ·) ∅

/-- An inventory marks an article strength when some entry marks it. -/
def Marks (p : DefiniteDescription.Strength) : Prop := ∃ e ∈ ds, e.Marks p

instance (p : DefiniteDescription.Strength) : Decidable (ds.Marks p) := by
  unfold Marks; infer_instance

theorem marks_singleton (e : Entry) (p : DefiniteDescription.Strength) : Marks [e] p ↔ e.Marks p :=
  ⟨fun ⟨_, he, h⟩ ↦ List.mem_singleton.mp he ▸ h, fun h ↦ ⟨e, List.mem_singleton_self e, h⟩⟩

private theorem mem_foldr_union {l : List Entry} {p : DefiniteDescription.Strength} :
    p ∈ (List.map Entry.strengths l).foldr (· ∪ ·) ∅ ↔ ∃ e ∈ l, p ∈ e.strengths := by
  induction l with
  | nil => simp
  | cons e es ih => simp [ih]

theorem marks_iff_mem_strengths (p : DefiniteDescription.Strength) :
    ds.Marks p ↔ p ∈ ds.strengths :=
  (mem_foldr_union (l := ds)).symm

/-- An inventory is syncretic when a single entry marks both strengths. -/
def IsSyncretic : Prop := ∃ e ∈ ds, e.IsSyncretic

instance : Decidable ds.IsSyncretic := by unfold IsSyncretic; infer_instance

/-! ### Realization -/

/-- An inventory realizes a kind of nominal description when it carries a form for it. A bare
nominal needs no determiner, a unique or anaphoric definite needs an entry marking its
strength, and an indefinite, demonstrative or possessive needs an entry of that kind. -/
def Realizes : NominalKind → Prop
  | .bare => True
  | .indefinite => ∃ e ∈ ds, e.kind = .article .indefinite
  | .unique => ds.Marks .uniqueness
  | .anaphoric => ds.Marks .familiarity
  | .demonstrative => ∃ e ∈ ds, e.kind = .demonstrative
  | .possessive => ∃ e ∈ ds, e.kind = .possessive

instance : DecidablePred ds.Realizes := fun k ↦ by cases k <;> unfold Realizes <;> infer_instance

theorem realizes_toKind (p : DefiniteDescription.Strength) : ds.Realizes p.toKind ↔ ds.Marks p := by
  cases p <;> exact Iff.rfl

end Inventory

end Determiner

/-! ### Article strengths -/

/-- The strengths an article admits are those its uses call for. A syncretic article such as
English *the* admits both, and a weak or strong article admits one. -/
def Article.strengths (a : Article) : Finset DefiniteDescription.Strength :=
  a.uses.image DefiniteDescription.Use.strength

theorem Article.mem_strengths_iff_marks (a : Article) (p : DefiniteDescription.Strength) :
    p ∈ a.strengths ↔ (Determiner.Entry.article a).Marks p :=
  Iff.rfl
