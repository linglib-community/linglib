module

public import Linglib.Syntax.Agreement.Target
public import Linglib.Languages.Romance.Italian.Gender

/-!
# Italian agreement targets

This file defines the Italian adjective as an agreement target, by its ending in each cell, and
derives what it inflects for.

A cell gives a person, a number and a gender, Italian adjectives distinguishing no case and no
definiteness. An adjective whose masculine singular ends in *-o* has the feminine singular *-a*,
the masculine plural *-i* and the feminine plural *-e*, as *furbo* 'crafty' does. It agrees with
its noun both when it modifies the noun and when it is in its predicate, so the one target occurs
at both positions.

## References

* [maiden-robustelli-2007]
-/

@[expose] public section

namespace Italian.Agreement

open _root_.Agreement Function

/-! ### Cells -/

/-- Italian distinguishes the singular and the plural. -/
def numberSystem : Finset Number := {.singular, .plural}

/-- The values Italian distinguishes in each dimension are the three persons, the singular and
the plural and the two genders, and it distinguishes no case and no definiteness. -/
abbrev Value : Dimension → Type
  | .person => Person
  | .number => numberSystem
  | .gender => Gender.Value
  | .case => Unit
  | .definiteness => Unit

/-- A cell of an Italian paradigm, a value in each dimension. -/
abbrev Cell := (d : Dimension) → Value d

/-- The third person masculine singular, the cell from which the witnesses of inflection
depart. -/
private def base : Cell
  | .person => .third
  | .number => ⟨.singular, by decide⟩
  | .gender => .masculine
  | .case => ()
  | .definiteness => ()

/-! ### The adjective -/

/-- The ending of an adjective whose masculine singular ends in *-o*, by gender and number. -/
def adjectiveEnding (g : Gender.Value) : numberSystem → String :=
  Number.elim numberSystem
    (match g with | .masculine => "-o" | .feminine => "-a")
    (match g with | .masculine => "-i" | .feminine => "-e")

/-- The adjective, used attributively and predicatively, inflects for gender and number. -/
def adjective : Target Value String :=
  .ofDependsOn {.attributive, .predicate} (fun x ↦ adjectiveEnding (x .gender) (x .number))
    {.gender, .number}
    (fun x y h ↦ by simp only [h .gender (by simp), h .number (by simp)])
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨⟨base, Gender.Value.feminine, by decide⟩, ⟨base, ⟨.plural, by decide⟩, by decide⟩⟩)

end Italian.Agreement
