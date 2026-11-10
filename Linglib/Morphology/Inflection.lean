/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Realization
public import Mathlib.Data.Set.Function

/-!
# Inflectional paradigms

An inflectional paradigm builds the forms of each lexeme at each cell from a stem, its lexical
material, and inflectional material, joined by one morphotactics. Corbett defines canonical
inflection by comparing them: across the cells of a lexeme the stem stays the same while the
inflectional material differs, and across lexemes at one cell the stems differ while the
inflectional material stays the same. A canonical paradigm satisfies the four comparisons and
realizes every cell by exactly one form. When forms decompose uniquely, [the comparisons entail
that every cell has its own form](##IsCanonical.leftUnique), as Stump observes, so that
[no lexeme is syncretic](##IsCanonical.not_isSyncretic), and a
canonical paradigm has [neither a suppletive stem nor a suppletive
affix](##IsCanonical.not_isSuppletive) and [the same inflectional material for every
lexeme](##IsCanonical.inflection_realize_eq).

## Implementation notes

The morphotactics is one function for every cell and lexeme, so Corbett's first row, the same
composition throughout, holds by construction. Theories supply the paradigm: Distributed
Morphology the exponents of a root and of the head beside it, Paradigm Function Morphology a
linkage's form correspondents and its realization rules. Two paradigms analyse the same forms
when their realizations are equal.

## References

* [corbett-2007]
* [stump-2016]
-/

@[expose] public section

namespace Morphology

open Function

/-- An **inflectional paradigm** builds the forms of each lexeme at each cell from pairs of a stem
and inflectional material, joined by the morphotactics `compose`. -/
structure InflectionalParadigm (L C Z I F : Type*) where
  /-- The pairs of a stem and inflectional material that build the forms of each cell. -/
  parts : Realization L C (Z × I)
  /-- The morphotactics joining a stem and inflectional material into a form. -/
  compose : Z → I → F

namespace InflectionalParadigm

variable {L C Z I F : Type*} (P : InflectionalParadigm L C Z I F)

/-- The forms of each cell, the morphotactics applied to its pairs. -/
def realization [DecidableEq F] : Realization L C F := P.parts.map (uncurry P.compose)

section Rows

variable [DecidableEq Z] [DecidableEq I]

/-- The lexical material of each cell, its stems. -/
def stem : Realization L C Z := P.parts.map Prod.fst

/-- The inflectional material of each cell. -/
def inflection : Realization L C I := P.parts.map Prod.snd

end Rows

/-- A paradigm is **unambiguous** when its morphotactics builds distinct forms from distinct pairs
of the paradigm. -/
def IsUnambiguous : Prop := Set.InjOn (uncurry P.compose) {x | ∃ l c, x ∈ P.parts.realize l c}

theorem isUnambiguous_iff : P.IsUnambiguous ↔ ∀ l c, ∀ x ∈ P.parts.realize l c, ∀ l' c',
    ∀ y ∈ P.parts.realize l' c', uncurry P.compose x = uncurry P.compose y → x = y :=
  ⟨fun h _ _ _ hx _ _ _ hy he ↦ h ⟨_, _, hx⟩ ⟨_, _, hy⟩ he,
    fun h _ ⟨_, _, hx⟩ _ ⟨_, _, hy⟩ he ↦ h _ _ _ hx _ _ _ hy he⟩

instance [Fintype L] [Fintype C] [DecidableEq Z] [DecidableEq I] [DecidableEq F] :
    Decidable P.IsUnambiguous :=
  decidable_of_iff _ P.isUnambiguous_iff.symm

theorem IsUnambiguous.of_injective2 (hc : Injective2 P.compose) : P.IsUnambiguous :=
  fun _ _ _ _ h ↦ Prod.ext (hc h).1 (hc h).2

variable [DecidableEq F] [DecidableEq Z] [DecidableEq I]

/-- A **canonical inflectional paradigm** ([corbett-2007], [stump-2016]) realizes every cell by
exactly one form, keeps a lexeme's stems the same across its cells and distinct between lexemes,
and keeps a cell's inflectional material distinct between the cells of a lexeme and the same
across lexemes. -/
structure IsCanonical : Prop where
  /-- Every cell of every lexeme has a form. -/
  isTotal : P.realization.IsTotal
  /-- No cell has more than one form. -/
  isUnivalent : P.realization.IsUnivalent
  /-- Each lexeme's stems are the same across its cells. -/
  stem_isInvariant : ∀ l, P.stem.IsInvariant l
  /-- No two lexemes share a stem at a cell. -/
  stem_leftUnique : ∀ c, Relator.LeftUnique (P.stem.transpose.Rel c)
  /-- No two cells of a lexeme share inflectional material. -/
  inflection_leftUnique : ∀ l, Relator.LeftUnique (P.inflection.Rel l)
  /-- Each cell's inflectional material is the same across lexemes. -/
  inflection_isInvariant : ∀ c, P.inflection.transpose.IsInvariant c

variable {P}

omit [DecidableEq Z] [DecidableEq I] in
/-- A form shared by two cells of an unambiguous paradigm comes from a pair of both cells. -/
theorem exists_mem_of_mem_realization (hP : P.IsUnambiguous) {l l' : L} {c c' : C} {w : F}
    (hw : w ∈ P.realization.realize l c) (hw' : w ∈ P.realization.realize l' c') :
    ∃ x ∈ P.parts.realize l c, x ∈ P.parts.realize l' c' := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hw
  obtain ⟨y, hy, he⟩ := Finset.mem_image.1 hw'
  exact ⟨x, hx, hP ⟨_, _, hy⟩ ⟨_, _, hx⟩ he ▸ hy⟩

/-- In an unambiguous canonical paradigm no two cells of a lexeme share a form, and no two lexemes
share a form at a cell, Corbett's comparison of outcomes. -/
theorem IsCanonical.leftUnique (h : P.IsCanonical) (hP : P.IsUnambiguous) :
    (∀ l, Relator.LeftUnique (P.realization.Rel l)) ∧
      ∀ c, Relator.LeftUnique (P.realization.transpose.Rel c) := by
  refine ⟨fun l c c' w hw hw' ↦ ?_, fun c l l' w hw hw' ↦ ?_⟩
  · obtain ⟨x, hx, hx'⟩ := exists_mem_of_mem_realization hP hw hw'
    exact h.inflection_leftUnique l (Finset.mem_image_of_mem Prod.snd hx)
      (Finset.mem_image_of_mem Prod.snd hx')
  · obtain ⟨x, hx, hx'⟩ := exists_mem_of_mem_realization hP hw hw'
    exact h.stem_leftUnique c (Finset.mem_image_of_mem Prod.fst hx)
      (Finset.mem_image_of_mem Prod.fst hx')

/-- An unambiguous canonical paradigm has no syncretic lexeme, and no cell at which two lexemes
share a form. -/
theorem IsCanonical.not_isSyncretic (h : P.IsCanonical) (hP : P.IsUnambiguous) :
    (∀ l, ¬ P.realization.IsSyncretic l) ∧ ∀ c, ¬ P.realization.transpose.IsSyncretic c :=
  ⟨fun l ↦ Realization.not_isSyncretic_iff.2 ((h.leftUnique hP).1 l),
    fun c ↦ Realization.not_isSyncretic_iff.2 ((h.leftUnique hP).2 c)⟩

/-- The lexemes of a canonical paradigm have the same inflectional material at every cell. -/
theorem IsCanonical.inflection_realize_eq (h : P.IsCanonical) (l l' : L) :
    P.inflection.realize l = P.inflection.realize l' :=
  have hl (l : L) (c : C) : P.inflection.transpose.IsLicensed c l :=
    Realization.isLicensed_map_iff.2 (Realization.isLicensed_map_iff.1 (h.isTotal l c))
  funext fun c ↦ (h.inflection_isInvariant c).realize_eq (hl l c) (hl l' c)

/-- A canonical paradigm has no suppletive stem, and no cell whose inflectional material is
suppletive across lexemes. -/
theorem IsCanonical.not_isSuppletive (h : P.IsCanonical) :
    (∀ l, ¬ P.stem.IsSuppletive l) ∧ ∀ c, ¬ P.inflection.transpose.IsSuppletive c :=
  ⟨fun l ↦ (h.stem_isInvariant l).not_isSuppletive,
    fun c ↦ (h.inflection_isInvariant c).not_isSuppletive⟩

end InflectionalParadigm

end Morphology
