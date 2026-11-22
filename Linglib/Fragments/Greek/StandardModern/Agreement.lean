module

public import Linglib.Syntax.Agreement.Target
public import Linglib.Fragments.Greek.StandardModern.Case
public import Linglib.Fragments.Greek.StandardModern.Gender

/-!
# Modern Greek agreement targets

This file defines the Modern Greek adjective as an agreement target, by its ending in each cell,
and derives what it inflects for.

A cell gives a person, a number, a gender and a case, Greek adjectives distinguishing no
definiteness. The commonest type of adjective, that of *ómorfos* 'beautiful', has in the masculine
the endings of the masculine nouns in *-os*, in the feminine those of the feminine nouns in *-i*
and in the neuter those of the neuter nouns in *-o*. An adjective modifies a noun attributively
or predicatively, and in either use it agrees in gender, number and case, so the one target
occurs at both positions.

## Implementation notes

The endings are written in the transliteration of `Greek.StandardModern.Declension`, in which
the feminine singular *-η* and the masculine plural *-οι* are both *-i*.

## References

* [holton-mackridge-philippaki-warburton-spyropoulos-2012]
-/

@[expose] public section

namespace Greek.StandardModern.Agreement

open _root_.Agreement Function

/-! ### Cells -/

/-- Modern Greek distinguishes the singular and the plural. -/
def numberSystem : Finset Number := {.singular, .plural}

/-- The values Modern Greek distinguishes in each dimension are the three persons, the singular
and the plural, the three genders and the four cases, and it distinguishes no definiteness. -/
abbrev Value : Dimension → Type
  | .person => Person
  | .number => numberSystem
  | .gender => Gender.Value
  | .case => Case
  | .definiteness => Unit

/-- A cell of a Modern Greek paradigm, a value in each dimension. -/
abbrev Cell := (d : Dimension) → Value d

/-- The third person masculine nominative singular, the cell from which the witnesses of
inflection depart. -/
private def base : Cell
  | .person => .third
  | .number => ⟨.singular, by decide⟩
  | .gender => .masculine
  | .case => .nom
  | .definiteness => ()

/-! ### The adjective -/

/-- The ending of an adjective in *-os*, *-i*, *-o* such as *ómorfos* 'beautiful', by gender,
number and case. -/
def adjectiveEnding (g : Gender.Value) (n : numberSystem) (c : Case) : String :=
  Number.elim numberSystem (n := n)
    (match g, c with
      | .masculine, .nom => "-os"
      | .masculine, .acc => "-o"
      | .masculine, .gen => "-u"
      | .masculine, .voc => "-e"
      | .feminine, .gen => "-is"
      | .feminine, _ => "-i"
      | .neuter, .gen => "-u"
      | .neuter, _ => "-o")
    (match g, c with
      | _, .gen => "-on"
      | .masculine, .acc => "-us"
      | .masculine, _ => "-i"
      | .feminine, _ => "-es"
      | .neuter, _ => "-a")

/-- The adjective, used attributively and predicatively, inflects for gender, number and
case. -/
def adjective : Target Value String :=
  .ofDependsOn {.attributive, .predicate}
    (fun x ↦ adjectiveEnding (x .gender) (x .number) (x .case)) {.gender, .number, .case}
    (fun x y h ↦ by simp only [h .gender (by simp), h .number (by simp), h .case (by simp)])
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨⟨base, Gender.Value.feminine, by decide⟩, ⟨base, ⟨.plural, by decide⟩, by decide⟩,
        ⟨base, Case.gen, by decide⟩⟩)

end Greek.StandardModern.Agreement
