/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.UD.Features
public import Linglib.Data.UD.UPOS
public import Linglib.Core.Order.Flat

/-!
# Word forms

This file defines the rows of a paper's word-level data: the lexemes, the form of a lexeme in a
cell, the relations, paradigms and root classes a source asserts over forms. The rows follow the
Wordlist module of the Cross-Linguistic Data Formats and the Paralex standard for lexicons of
inflected forms, which shares its column names. It is the morphological counterpart of
`Data/Examples/`: the datum is a word and its parts rather than an utterance and its gloss.

## Main definitions

* `CLDF.Wordlist.Lexeme`: a row of the `LexemeTable`, a word of a language by the concept it
  expresses.
* `CLDF.Wordlist.Form`: a row of the `FormTable`, the form of a lexeme in a cell, with the source's
  segmentation and its judgment of the form.
* `CLDF.Wordlist.FormRelation`: a row of the `FormRelationTable`, a relation a source asserts from
  one form to another.
* `CLDF.Wordlist.Paradigm`: a row of the `ParadigmTable`, the forms a source gives a lexeme as one
  column of its table.
* `CLDF.Wordlist.RootClasses`: a row of the `RootClassTable`, a source's judgment that the cells of
  a paradigm divide into classes sharing a root.

## Implementation notes

* Per-paper data lives in `Linglib/Data/Wordlist/{AuthorYear}.json` and is compiled by
  `scripts/gen_wordlist.py` into `{AuthorYear}.lean`, declaring `namespace {AuthorYear}.Forms`: a
  `Cell` type, the lexemes, forms, relations, paradigms and root classes, the lists `all` of the
  forms the sources accept and `marked` of the others, and an `Analysis` table.
* A cell is a bundle of features. Universal Dependencies features are typed by
  `UD.MorphFeatures`; a dataset whose cells need features UD lacks extends it with generated
  enumerations, so `Form` is parametric in its cell type and `Form.map` changes it.
* A form carries the source's judgment of it in its cell, CLDF's `grammaticalityJudgement`: a
  form a source rejects is a row of its own, so disagreeing sources sit side by side.
* `segments` is the source's tokenization of the form into sound segments, at the source's
  granularity; `morphs` is the morph segmentation the source prints, `ø` marking a null exponent.
* Root identity is a judgment rather than a function of the forms: *better* and *best* share a
  root that no identity of strings shows, so a source's classes are rows of their own.
* What a paper's theory assigns to a form, such as an underlying representation, a root or a
  class, is that paper's parse and goes to the generated `Analysis` table, never to the form.
  The generator resolves every reference to an analysis, as it resolves every reference to a
  form: each form `x` has its analysis `x.analysis`, and a dataset with relations and analyses
  has its relations over the analyses too, so no study joins rows by identifier.
* Comments, the `ParameterTable` and the cognates a source lists are its record: the generator
  validates them and does not emit them.

## TODO

* Cite the paper that introduces the Paralex standard (Beniamine and colleagues, 2023) once its
  bibliographic record is verified.

## References

* [forkel-etal-2018]
* [forkel-etal-2024]
-/

@[expose] public section

namespace CLDF.Wordlist

/-- A `Lexeme` is a row of the `LexemeTable`, a word of a language, by the concept it expresses
and its citation form. -/
structure Lexeme where
  /-- The `ID` column holds a stable identifier keyed to the paper. -/
  id : String
  /-- The `Language_ID` column holds the Glottocode of the language. -/
  languageId : Glottocode
  /-- The `Variety` column names the variety, where the source distinguishes varieties of one
  Glottolog languoid. -/
  variety : String := ""
  /-- The `Parameter_ID` column names the concept the lexeme expresses. -/
  parameterId : String
  /-- The `Name` column holds the citation form, where the source gives one. -/
  label : String := ""
  /-- The `POS` column holds the part of speech, where the source gives one. -/
  pos : Flat UD.UPOS := ⊥
  deriving DecidableEq, Repr

/-- A `Form C` is a row of the `FormTable`, the form of a lexeme in a cell of type `C`, with the
source's segmentation and its judgment of the form. -/
structure Form (C : Type*) where
  /-- The `ID` column holds a stable identifier keyed to the paper. -/
  id : String
  /-- The lexeme the `Lexeme_ID` column names. -/
  lexeme : Lexeme
  /-- The cell the `Cell` column names. -/
  cell : C
  /-- The `Form` column holds the written form. -/
  form : String
  /-- The `Segments` column holds the form's sound segments. -/
  segments : List String := []
  /-- The `Morphs` column holds the form's morphs as the source segments it. -/
  morphs : List String := []
  /-- The `Judgment` column holds the source's mark on the form in its cell. -/
  judgment : Judgment := .acceptable
  /-- The `Source` column holds the references, each a bibkey with a locator. -/
  source : List SourceRef := []
  deriving DecidableEq, Repr

namespace Form

variable {C D E : Type*}

/-- The Glottocode of the form's language. -/
abbrev languageId (f : Form C) : Glottocode := f.lexeme.languageId

/-- The concept the form expresses. -/
abbrev parameterId (f : Form C) : String := f.lexeme.parameterId

/-- `f.map g` is `f` with its cell read through `g`. -/
def map (g : C → D) (f : Form C) : Form D := { f with cell := g f.cell }

@[simp] theorem map_id (f : Form C) : f.map _root_.id = f := rfl

@[simp] theorem map_map (g : C → D) (h : D → E) (f : Form C) :
    (f.map g).map h = f.map (h ∘ g) := rfl

/-- `f.slots` reads the segments of `f` as a slot-indexed item on the flat carrier, the shape
the schemas of `Morphology/ConstructionMorphology/` match. -/
def slots (f : Form C) (i : Fin f.segments.length) : Flat String := ↑f.segments[i]

/-- `f.morphSlots` reads the morphs of `f` as a slot-indexed item on the flat carrier, one morph
per slot. -/
def morphSlots (f : Form C) (i : Fin f.morphs.length) : Flat String := ↑f.morphs[i]

end Form

/-- A `FormRelation α` is a row of the `FormRelationTable`, a relation that a source asserts from
one form to another, named by its term for it, with each form given as an `α`: the form itself,
or its analysis. -/
structure FormRelation (α : Type*) where
  /-- The `ID` column holds the relation's identifier. -/
  id : String
  /-- The form that the `Form_ID` column names. -/
  form : α
  /-- The form that the `Target_ID` column names. -/
  target : α
  /-- The `Relation` column holds the source's name for the relation. -/
  relation : String
  /-- The `Source` column holds the references, each a bibkey with a locator. -/
  source : List SourceRef := []
  deriving DecidableEq, Repr

/-- A `Paradigm C` is a row of the `ParadigmTable`, the forms a source gives a lexeme as one
column of its table, at most one to a cell. -/
structure Paradigm (C : Type*) where
  /-- The `ID` column holds a stable identifier keyed to the paper. -/
  id : String
  /-- The lexeme whose forms these are. -/
  lexeme : Lexeme
  /-- The forms that the `Form_IDs` column names. -/
  forms : List (Form C)
  /-- The `Source` column holds the references, each a bibkey with a locator. -/
  source : List SourceRef := []
  deriving DecidableEq, Repr

/-- A `RootClasses C` is a row of the `RootClassTable`, a source's judgment that the cells of a
paradigm divide into classes of cells whose forms share a root, each cell with the index of its
class. -/
structure RootClasses (C : Type*) extends Paradigm C where
  /-- The class of each cell, `A` as `0`, `B` as `1`, and so on. -/
  classes : List (C × ℕ)
  deriving DecidableEq, Repr

/-- `r.classOf c` is the class of the cell `c` in the judgment `r`, if `r` classes `c`. -/
def RootClasses.classOf {C : Type*} [DecidableEq C] (r : RootClasses C) (c : C) : Option ℕ :=
  r.classes.lookup c

end CLDF.Wordlist
