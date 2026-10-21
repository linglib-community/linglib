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
`Article`, `DemonstrativeDeterminer`, `Quantifier` and `PossessiveDeterminer` extend
it. An inventory is
a list of `Determiner.Entry` occurrences, and the typologies of definiteness marking are
derived from it rather than declared. An entry marks an article strength when one of the
definite uses it obligatorily expones calls for that strength, and a language's marking type,
after Jenks and Moroney, and its article system, after Patel-Grosz and Grosz, are theorems about
its inventory, discharged by `decide`.

## Main declarations

* `Determiner` is the base record, and `Determiner.toWord` realizes it as a word.
* `Article` records definiteness, the exponent and the definite uses the article obligatorily
  expones; `DemonstrativeDeterminer`, `Quantifier` and `PossessiveDeterminer` are the
  other specializations.
* `Determiner.Entry` is an occurrence of one of the four kinds in an inventory, `Entry.kind`
  is its kind together with an article's definiteness, and `Entry.Marks` says which strengths
  it marks.
* `Determiner.Inventory` is a language's declared inventory. `Inventory.Marks` and
  `Inventory.IsSyncretic` lift the entry predicates, and `Inventory.markingStrategy` and
  `Inventory.articleType` derive the typological cells, each characterized by an `_iff` lemma.
* `Determiner.Inventory.Realizes` says that the inventory carries a form for a kind of nominal
  description.
* `Article.strengths` is the set of strengths an article admits.

## Implementation notes

This file is the Frame-free lexical layer. The denotations of articles, demonstratives and
possessives are in `Semantics/Reference/Determiner.lean`, and the generalized-quantifier
denotation of a `Quantifier` is supplied by its consumers. `Inventory` is a `def`
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

open Reference

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
  uses : Finset Description.Use := ∅
  deriving DecidableEq

/-- A demonstrative determiner carries its deictic content, the participant sets of the referents
in whose vicinity it locates its referent. Its `uses` are the definite uses it obligatorily
expones, as Mandarin *na* expones the anaphoric use, and they are empty for a demonstrative that
merely can be used anaphorically. -/
structure DemonstrativeDeterminer extends Determiner where
  /-- The participant sets of the referents in whose vicinity the form locates its referent. -/
  deixis : Finset (Finset Discourse.Role)
  /-- The definite uses the demonstrative obligatorily expones. -/
  uses : Finset Description.Use := ∅
  deriving DecidableEq

/-- A quantificational determiner records only what its generalized-quantifier denotation
leaves open, the grammatical number it selects and whether it selects mass nouns, since
synonymous determiners such as *every* and *all* differ there. Everything the denotation fixes,
its force, monotonicity, strength and conservativity, is a theorem about the denotation, which
the consumers supply. -/
structure Quantifier extends Determiner where
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
  | quantifier (q : Quantifier)
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

/-- The definite uses an entry obligatorily expones are an article's `uses` and a
demonstrative's `uses`; a quantifier or possessive expones none. -/
def uses : Entry → Finset Description.Use
  | .article a => a.uses
  | .demonstrative d => d.uses
  | .quantifier _ | .possessive _ => ∅

variable (e : Entry)

/-- An entry marks an article strength when some definite use it expones calls for it. -/
def Marks (p : Description.Strength) : Prop := ∃ u ∈ e.uses, u.strength = p

instance (p : Description.Strength) : Decidable (e.Marks p) := by unfold Marks; infer_instance

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

/-- An inventory marks an article strength when some entry marks it. -/
def Marks (p : Description.Strength) : Prop := ∃ e ∈ ds, e.Marks p

instance (p : Description.Strength) : Decidable (ds.Marks p) := by unfold Marks; infer_instance

/-- A one-entry inventory marks a strength iff the entry marks it. -/
theorem marks_singleton (e : Entry) (p : Description.Strength) : Marks [e] p ↔ e.Marks p :=
  ⟨fun ⟨_, he, h⟩ ↦ List.mem_singleton.mp he ▸ h, fun h ↦ ⟨e, List.mem_singleton_self e, h⟩⟩

/-- An inventory is syncretic when a single entry marks both strengths, which separates the
generally marked cell from the bipartite one. -/
def IsSyncretic : Prop := ∃ e ∈ ds, e.IsSyncretic

instance : Decidable ds.IsSyncretic := by unfold IsSyncretic; infer_instance

/-! ### The marking typology

A language's [jenks-2018] type, or [moroney-2021]'s unmarked type, is a theorem about its
inventory, and each type is characterized by its `markingStrategy_eq_*_iff` lemma. An inventory
with a form that marks both strengths is generally marked; otherwise the type is fixed by which
strengths it marks, both by distinct forms, familiarity alone, uniqueness alone, or neither. -/

section

variable {ds}

/-- A syncretic inventory marks both strengths. -/
theorem IsSyncretic.marks (h : ds.IsSyncretic) (p : Description.Strength) : ds.Marks p :=
  let ⟨e, he, hu, hf⟩ := h
  ⟨e, he, by cases p; exacts [hu, hf]⟩

end

/-- The definiteness-marking type derived from an inventory. -/
def markingStrategy : MarkingStrategy :=
  if ds.IsSyncretic then .generallyMarked
  else if ds.Marks .uniqueness then
    if ds.Marks .familiarity then .bipartite else .markedUnique
  else if ds.Marks .familiarity then .markedAnaphoric else .unmarked

section

variable {ds}

theorem markingStrategy_eq_generallyMarked_iff :
    ds.markingStrategy = .generallyMarked ↔ ds.IsSyncretic := by
  unfold markingStrategy; split_ifs <;> simp_all

theorem markingStrategy_eq_bipartite_iff :
    ds.markingStrategy = .bipartite ↔
      ds.Marks .uniqueness ∧ ds.Marks .familiarity ∧ ¬ds.IsSyncretic := by
  unfold markingStrategy; split_ifs <;> simp_all

theorem markingStrategy_eq_markedUnique_iff :
    ds.markingStrategy = .markedUnique ↔ ds.Marks .uniqueness ∧ ¬ds.Marks .familiarity := by
  unfold markingStrategy; split_ifs <;> simp_all [IsSyncretic.marks]

theorem markingStrategy_eq_markedAnaphoric_iff :
    ds.markingStrategy = .markedAnaphoric ↔ ¬ds.Marks .uniqueness ∧ ds.Marks .familiarity := by
  unfold markingStrategy; split_ifs <;> simp_all [IsSyncretic.marks]

theorem markingStrategy_eq_unmarked_iff :
    ds.markingStrategy = .unmarked ↔ ¬ds.Marks .uniqueness ∧ ¬ds.Marks .familiarity := by
  unfold markingStrategy; split_ifs <;> simp_all [IsSyncretic.marks]

end

/-- The article system of an inventory ([patel-grosz-grosz-2017]) is the coarsening
`MarkingStrategy.articleType` of its marking type. -/
def articleType : ArticleType := ds.markingStrategy.articleType

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

/-- An inventory realizes the kind of an article strength iff it marks that strength. -/
theorem realizes_toKind (p : Description.Strength) : ds.Realizes p.toKind ↔ ds.Marks p := by
  cases p <;> exact Iff.rfl

end Inventory

end Determiner

/-! ### Article strengths -/

/-- The strengths an article admits are those its uses call for. A syncretic article such as
English *the* admits both, and a weak or strong article admits one. -/
def Article.strengths (a : Article) : Finset Description.Strength :=
  a.uses.image Description.Use.strength

/-- An article admits a strength iff, as an entry, it marks that strength. -/
theorem Article.mem_strengths_iff_marks (a : Article) (p : Description.Strength) :
    p ∈ a.strengths ↔ (Determiner.Entry.article a).Marks p :=
  Finset.mem_image
