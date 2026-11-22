module

public import Linglib.Syntax.Agreement.Target
public import Linglib.Fragments.Dutch.Adjectives

/-!
# Dutch agreement targets

This file defines the Dutch adjective as an agreement target, by whether it takes the ending
*-e* in each cell, and derives what it inflects for.

A cell gives a person, a number, a gender and a definiteness, Dutch adjectives distinguishing no
case. The attributive adjective takes the ending unless its noun phrase is indefinite and its
head noun neuter and not plural, so it inflects for definiteness, gender and number. The
predicative adjective has no ending and inflects for nothing.

## References

* [broekhuis-corver-2026d]
-/

@[expose] public section

namespace Dutch.Agreement

open _root_.Agreement Function

/-! ### Cells -/

/-- The values Dutch distinguishes in each dimension are the three persons, the numbers, the
common gender and the neuter, and the definiteness of the noun phrase, and it distinguishes no
case. -/
abbrev Value : Dimension → Type
  | .person => Person
  | .number => Number
  | .gender => Gender.Value
  | .case => Unit
  | .definiteness => Definiteness

/-- A cell of a Dutch paradigm, a value in each dimension. -/
abbrev Cell := (d : Dimension) → Value d

/-- The third person indefinite neuter singular, the one cell of the attributive adjective
without the ending. -/
private def base : Cell
  | .person => .third
  | .number => .singular
  | .gender => .neuter
  | .case => ()
  | .definiteness => .nonSpecific

/-! ### The adjective -/

/-- The attributive ending, the schwa written *-e*, or none. -/
inductive Ending where
  | schwa
  | zero
  deriving DecidableEq, Repr, Fintype

/-- The ending of an attributive adjective that declines. -/
def ending (d : Definiteness) (g : Gender.Value) (n : Number) : Ending :=
  if Adjectives.TakesEnding d g n then .schwa else .zero

theorem ending_eq_schwa_iff {d : Definiteness} {g : Gender.Value} {n : Number} :
    ending d g n = .schwa ↔ Adjectives.TakesEnding d g n := by
  simp [ending]

/-- The attributive adjective inflects for definiteness, gender and number. -/
def attributiveAdjective : Target Value Ending :=
  .ofDependsOn {.attributive} (fun x ↦ ending (x .definiteness) (x .gender) (x .number))
    {.definiteness, .gender, .number}
    (fun x y h ↦ by
      simp only [h .definiteness (by simp), h .gender (by simp), h .number (by simp)])
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨⟨base, Definiteness.definite, by decide⟩, ⟨base, Gender.Value.common, by decide⟩,
        ⟨base, Number.plural, by decide⟩⟩)

/-- The predicative adjective has no ending and inflects for nothing. -/
def predicativeAdjective : Target Value Ending :=
  .ofDependsOn {.predicate} (fun _ ↦ .zero) ∅ (fun _ _ _ ↦ rfl) (by simp)

end Dutch.Agreement
