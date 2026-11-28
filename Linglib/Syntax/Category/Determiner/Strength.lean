/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Finset.Union
public import Linglib.Syntax.Category.Determiner.Basic

/-!
# The strengths of an article

Schwarz sorts the uses of a definite description under two strengths. The weak article of German
and Fering, which presupposes uniqueness, has the situational uses and part-whole bridging, and
the strong article, which presupposes familiarity, has the anaphoric use and relational bridging.
This file reads the strengths an article marks off the uses it expones: an article marks a
strength when it has a use that calls for it. An article that marks both, as English *the* does,
is syncretic.

Whether an article has every use its strengths call for is an empirical question about the
article, which a study states of the articles it treats. A demonstrative marks no strength:
whether a language's demonstrative is obligatory in a definite use follows from a theory of
competition between forms, as in Jenks's account of Mandarin.

## Main definitions

* `Article.strengths`: the strengths an article marks.
* `Determiner.Entry.strengths`, `Determiner.Entry.IsSyncretic`: the strengths of an entry, and an
  entry that marks both.
* `Determiner.Inventory.strengths`, `Determiner.Inventory.IsSyncretic`: the strengths the entries
  of an inventory mark, and an inventory with a syncretic entry.

## References

* [schwarz-2009]
* [schwarz-2013]
* [jenks-2018]
-/

@[expose] public section

/-- The strengths an article marks are those its uses call for. A syncretic article such as
English *the* marks both, and a weak or strong article marks one. -/
def Article.strengths (a : Article) : Finset Definite.Strength :=
  a.uses.image Definite.Use.strength

namespace Determiner

namespace Entry

variable (e : Entry)

/-- The strengths an entry marks are an article's; a demonstrative, quantifier or possessive
marks none by its lexicon. -/
def strengths : Finset Definite.Strength := e.uses.image Definite.Use.strength

@[simp] theorem strengths_article (a : Article) : (article a).strengths = a.strengths := rfl

@[simp] theorem strengths_demonstrative (d : DemonstrativeDeterminer) :
    (demonstrative d).strengths = ∅ := rfl

@[simp] theorem strengths_quantifier (q : QuantificationalDeterminer) :
    (quantifier q).strengths = ∅ := rfl

@[simp] theorem strengths_possessive (p : PossessiveDeterminer) :
    (possessive p).strengths = ∅ := rfl

/-- An entry is syncretic when it marks both strengths, as English *the* does. -/
def IsSyncretic : Prop := e.strengths = Finset.univ

instance : Decidable e.IsSyncretic := inferInstanceAs (Decidable (_ = _))

end Entry

namespace Inventory

variable (ds : Inventory)

/-- The strengths an inventory marks are those its entries mark. -/
def strengths : Finset Definite.Strength := (ds.map Entry.strengths).toFinset.biUnion id

variable {ds} in
theorem mem_strengths {p : Definite.Strength} :
    p ∈ ds.strengths ↔ ∃ e ∈ ds, p ∈ e.strengths := by
  simp [strengths]

/-- An inventory is syncretic when a single entry marks both strengths. -/
def IsSyncretic : Prop := ∃ e ∈ ds, e.IsSyncretic

instance : Decidable ds.IsSyncretic := inferInstanceAs (Decidable (∃ e ∈ ds, e.IsSyncretic))

end Inventory

end Determiner
