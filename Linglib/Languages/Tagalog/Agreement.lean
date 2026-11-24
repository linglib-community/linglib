module

public import Mathlib.Data.Finset.Insert
public import Linglib.Syntax.Agreement.Target
public import Linglib.Languages.Tagalog.Case

/-!
# Tagalog agreement targets

This file defines the Tagalog *ma-* adjective as an agreement target, by the forms it may take
in each cell, and derives what it inflects for.

Many *ma-* adjectives have a plural form with a duplicating syllable between *ma-* and the base,
*maganda* 'beautiful', *magaganda*. The use of the plural form is in general optional, so with
a plural the adjective takes either form, and the form of a cell is the set of the forms it
admits. The adjective occurs as a predicate and, before the linker, as a modifier, and inflects
for number. Most *ma-* adjectives whose base is a concrete noun, *madahon* 'leafy', have no
plural form and inflect for nothing.

## Implementation notes

The plural marker *mga*, which may precede an adjective, is a word of its own and no form of the
adjective. After *mga* most speakers require the plural form, which the cells do not record.

## References

* [schachter-otanes-1972]
-/

@[expose] public section

namespace Tagalog.Agreement

open _root_.Agreement Function

/-! ### Cells -/

/-- Tagalog distinguishes the singular and the plural. -/
def numberSystem : Finset Number := {.singular, .plural}

/-- The values Tagalog distinguishes in each dimension are the three persons, the singular and
the plural and the three cases, and it distinguishes no gender and no definiteness. -/
abbrev Value : Dimension → Type
  | .person => Person
  | .number => numberSystem
  | .gender => Unit
  | .case => Case
  | .definiteness => Unit

/-- A cell of a Tagalog paradigm, a value in each dimension. -/
abbrev Cell := (d : Dimension) → Value d

/-- The third person singular, the cell from which the witness of inflection departs. -/
private def base : Cell
  | .person => .third
  | .number => ⟨.singular, by decide⟩
  | .gender => ()
  | .case => .ang
  | .definiteness => ()

/-! ### The *ma-* adjective -/

/-- The forms of a *ma-* adjective: the plain form and the plural form with a duplicating
syllable. -/
inductive MaForm where
  /-- The plain form, *maganda*. -/
  | plain
  /-- The plural form, *magaganda*. -/
  | duplicated
  deriving DecidableEq, Repr, Fintype

/-- The forms a pluralizable *ma-* adjective may take with a number: the plain form with the
singular, and either form with the plural. -/
def maForms : numberSystem → Finset MaForm :=
  Number.elim numberSystem {.plain} {.plain, .duplicated}

/-- The pluralizable *ma-* adjective, used as a modifier and as a predicate, inflects for
number. -/
def maAdjective : Target Value (Finset MaForm) :=
  .ofDependsOn {.attributive, .predicate} (fun x ↦ maForms (x .number)) {.number}
    (fun x y h ↦ by simp only [h .number (by simp)])
    (by
      simp only [Finset.mem_singleton, forall_eq]
      exact ⟨base, ⟨.plural, by decide⟩, by decide⟩)

/-- A *ma-* adjective without a plural form, used as a modifier and as a predicate, inflects for
nothing. -/
def invariableMaAdjective : Target Value (Finset MaForm) :=
  .ofDependsOn {.attributive, .predicate} (fun _ ↦ {.plain}) ∅ (fun _ _ _ ↦ rfl) (by simp)

end Tagalog.Agreement
