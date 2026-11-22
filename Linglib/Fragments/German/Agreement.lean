module

public import Linglib.Syntax.Agreement.Target
public import Linglib.Fragments.German.Adjectives

/-!
# German agreement targets

This file defines the German adjective as an agreement target, by its ending in each cell, and
derives what it inflects for.

A cell gives a person, a number, a gender and a case, German adjectives distinguishing no
definiteness of their own. The attributive adjective takes the strong or the weak endings
according to the determiner before it, and with either set it inflects for gender, number and
case. The predicative adjective has no ending and inflects for nothing.

## Implementation notes

The choice between the strong and the weak endings depends on the determiner of the noun phrase
and not on a value of the controller, so the two sets are two targets and not one target with a
further dimension.

## References

* [durrell-2011]
-/

@[expose] public section

namespace German.Agreement

open _root_.Agreement Function

/-! ### Cells -/

/-- German distinguishes the singular and the plural. -/
def numberSystem : Finset Number := {.singular, .plural}

/-- The values German distinguishes in each dimension are the three persons, the singular and the
plural, the three genders and the four cases, and it distinguishes no definiteness. -/
abbrev Value : Dimension → Type
  | .person => Person
  | .number => numberSystem
  | .gender => Gender.Value
  | .case => Case
  | .definiteness => Unit

/-- A cell of a German paradigm, a value in each dimension. -/
abbrev Cell := (d : Dimension) → Value d

/-- The gender and number of a cell, gender being distinguished in the singular alone. -/
def genderNumber (x : Cell) : GenderNumber :=
  Number.elim numberSystem (n := x .number) (.sg (x .gender)) .pl

/-- The third person masculine nominative singular, the cell from which the witnesses of
inflection depart. -/
private def base : Cell
  | .person => .third
  | .number => ⟨.singular, by decide⟩
  | .gender => .masc
  | .case => .nom
  | .definiteness => ()

/-! ### The adjective -/

/-- The adjective with the strong endings, used attributively, inflects for gender, number and
case. -/
def strongAdjective : Target Value String :=
  .ofDependsOn {.attributive} (fun x ↦ Adjectives.strong (genderNumber x) (x .case))
    {.gender, .number, .case}
    (fun x y h ↦ by
      simp only [genderNumber, h .gender (by simp), h .number (by simp), h .case (by simp)])
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨⟨base, Gender.Value.fem, by decide⟩, ⟨base, ⟨.plural, by decide⟩, by decide⟩,
        ⟨base, Case.gen, by decide⟩⟩)

/-- The adjective with the weak endings, used attributively, inflects for gender, number and
case. -/
def weakAdjective : Target Value String :=
  .ofDependsOn {.attributive} (fun x ↦ Adjectives.weak (genderNumber x) (x .case))
    {.gender, .number, .case}
    (fun x y h ↦ by
      simp only [genderNumber, h .gender (by simp), h .number (by simp), h .case (by simp)])
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨⟨update base .case Case.acc, Gender.Value.fem, by decide⟩,
        ⟨base, ⟨.plural, by decide⟩, by decide⟩, ⟨base, Case.acc, by decide⟩⟩)

/-- The predicative adjective has no ending and inflects for nothing. -/
def predicativeAdjective : Target Value String :=
  .ofDependsOn {.predicate} (fun _ ↦ "") ∅ (fun _ _ _ ↦ rfl) (by simp)

end German.Agreement
