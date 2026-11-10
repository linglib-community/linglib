module

public import Linglib.Semantics.Composition.Interpreter.Effect

/-!
# The base sorts and their domains

The semantic types of the library are the types over six sorts of things: truth values, which
every type grammar has, and the entities, worlds, degrees, cardinalities and eventualities of
two-sorted type theory and its extensions. An intension is a function from worlds. The domain of
a type is fixed by a set of entities, a set of worlds, and the carriers of the degrees and the
eventualities.

## Main definitions

* `Interpreter.Base`: the base sorts.
* `Interpreter.Ty.intens`: intensions, the functions from worlds.
* `Interpreter.Sorts`: the carriers of the degree and eventuality sorts.
* `Interpreter.Ty.Domain`: the domain of a type over entities `E` and worlds `W`.
* `Interpreter.Denotation`: a type with a value in its domain.

## References

* [montague-1973]
* [gallin-1975]
* [heim-2001]
* [davidson-1967]
-/

@[expose] public section

namespace Interpreter

/-- The base sorts: entities, degrees ([heim-2001]), cardinalities, eventualities
([davidson-1967]), events and states alike, and worlds, the indices of evaluation
([gallin-1975]). -/
inductive Base where
  /-- Entities. -/
  | e
  /-- Degrees, denoting in a model's scale. -/
  | d
  /-- Cardinalities, denoting in `ℕ`. -/
  | n
  /-- Eventualities. -/
  | v
  /-- Worlds, or situations. -/
  | s
  deriving DecidableEq, Repr

namespace Ty

/-- Entities. -/
@[match_pattern] abbrev e : Ty Base := .base .e
/-- Degrees. -/
@[match_pattern] abbrev d : Ty Base := .base .d
/-- Cardinalities. -/
@[match_pattern] abbrev n : Ty Base := .base .n
/-- Eventualities. -/
@[match_pattern] abbrev v : Ty Base := .base .v
/-- Worlds. -/
@[match_pattern] abbrev s : Ty Base := .base .s

/-- Intensions `⟨s,a⟩`, the functions from worlds. -/
@[match_pattern] abbrev intens (a : Ty Base) : Ty Base := .fn .s a

/-- `⟨e,t⟩`, properties of individuals. -/
abbrev et : Ty Base := .fn .e .t
/-- `⟨e,⟨e,t⟩⟩`, relations between individuals. -/
abbrev eet : Ty Base := .fn .e (.fn .e .t)
/-- `⟨v,t⟩`, predicates of eventualities. -/
abbrev vt : Ty Base := .fn .v .t
/-- `⟨e,⟨v,t⟩⟩`, relations of individuals to eventualities, as thematic roles are. -/
abbrev evt : Ty Base := .fn .e (.fn .v .t)
/-- `⟨⟨e,t⟩,t⟩`, generalized quantifiers. -/
abbrev ett : Ty Base := .fn (.fn .e .t) .t
/-- `⟨⟨e,t⟩,⟨⟨e,t⟩,t⟩⟩`, determiners. -/
abbrev det : Ty Base := .fn (.fn .e .t) (.fn (.fn .e .t) .t)

end Ty

/-- The carriers of the sorts beyond entities and worlds, the scale of degrees and the
eventualities, which are empty unless a model supplies them. -/
structure Sorts where
  /-- The scale of degrees. -/
  degree : Type := Empty
  /-- The eventualities. -/
  eventuality : Type := Empty

/-- The domain of a base sort over entities `E` and worlds `W`. -/
abbrev Base.Dom (E W : Type) (S : Sorts := {}) : Base → Type
  | .e => E
  | .d => S.degree
  | .n => ℕ
  | .v => S.eventuality
  | .s => W

/-- The domain of a type over entities `E` and worlds `W`. -/
abbrev Ty.Domain (E W : Type) (ty : Ty Base) (S : Sorts := {}) : Type :=
  ty.Dom (Base.Dom E W S)

/-- A denotation: a semantic type with a value in its domain. -/
abbrev Denotation (E W : Type) (S : Sorts := {}) : Type :=
  (ty : Ty Base) × ty.Domain E W S

end Interpreter
