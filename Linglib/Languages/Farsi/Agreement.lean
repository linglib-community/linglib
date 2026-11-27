module

public import Linglib.Syntax.Agreement.Target

/-!
# Persian agreement targets

This file defines the Persian adjective as an agreement target. Neither an attributive nor a
predicative adjective shows any form of agreement, so the adjective has one form in every cell
and inflects for nothing.

## References

* [mahootian-1997]
-/

@[expose] public section

namespace Farsi.Agreement

open _root_.Agreement

/-- Persian distinguishes the singular and the plural. -/
def numberSystem : Finset Number := {.singular, .plural}

/-- The values Persian distinguishes in each dimension are the three persons and the singular
and the plural, and it distinguishes no gender, no case and no definiteness. -/
abbrev Value : Dimension → Type
  | .person => Person
  | .number => numberSystem
  | .gender => Unit
  | .case => Unit
  | .definiteness => Unit

/-- A cell of a Persian paradigm, a value in each dimension. -/
abbrev Cell := (d : Dimension) → Value d

/-- The adjective, used attributively and predicatively, has no ending and inflects for
nothing. -/
def adjective : Target Value String :=
  .ofDependsOn {.attributive, .predicate} (fun _ ↦ "") ∅ (fun _ _ _ ↦ rfl) (by simp)

end Farsi.Agreement
