module

/-!
# Degree constructions

This file defines `Degree.Construction`, the surface forms a gradable
predicate can appear in — bare positive, comparative, equative, measure
phrase, and degree question ([beck-2011], [rett-2015b]). The Deg⁰ head
inventory is defined in `Linglib/Syntax/Category/Degree/Basic.lean`.
-/

@[expose] public section

namespace Degree

/-- A surface degree construction built on a gradable predicate. -/
inductive Construction where
  /-- "Kim is tall" — unmarked form. -/
  | positive
  /-- "Kim is taller than Sam". -/
  | comparative
  /-- "Kim is as tall as Sam". -/
  | equative
  /-- "Kim is 6 feet tall" — explicit measure phrase. -/
  | measurePhrase
  /-- "How tall is Kim?". -/
  | degreeQuestion
  deriving DecidableEq, Repr

/-- Bare lowercase construction names for diagnostic messages, distinct
from `Repr` (which prefixes the namespace). -/
instance : ToString Construction where
  toString
    | .positive => "positive"
    | .comparative => "comparative"
    | .equative => "equative"
    | .measurePhrase => "measurePhrase"
    | .degreeQuestion => "degreeQuestion"

end Degree
