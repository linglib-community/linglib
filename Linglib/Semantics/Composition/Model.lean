module

public import Linglib.Semantics.Composition.Ty
public import Mathlib.ModelTheory.Basic

/-!
# Models for type-driven composition

A *model* for a first-order fragment has a domain of individuals, a set of worlds, and at each
world an interpretation of the fragment's names and predicates: a name denotes an individual
there, and a predicate the individuals, or pairs of individuals, that it holds of there. The
individuals are the same at every world, as in a constant-domain Kripke model, while what a
predicate holds of varies from world to world. The words of a first-order fragment translate to
the model's symbols in `Composition/FirstOrder.lean`.

## Main definitions

* `Montague.Model`: an entity domain `E`, worlds `W`, and a structure `interp w` at each world.
* `Montague.Model.const`, `Montague.Model.pred₁`, `Montague.Model.pred₂`: the denotations of a
  constant and of unary and binary relation symbols at a world.

## Implementation notes

The interpretation at a world is a mathlib first-order structure `L.Structure E`, carried as a
term rather than an instance, since a family of structures on one carrier indexed by worlds
cannot be found by instance search. Symbols are read off through `Structure.funMap` and
`Structure.RelMap`, as DRT reads off the truth of atomic conditions (`Semantics/Dynamic/DRS/`),
and a formula is realized at a world by `Formula.RealizeAt m.interp w`. The concrete toy model of
`Studies/HeimKratzer1998` follows mathlib's concrete-language idiom.

## References

* [heim-kratzer-1998]
-/

@[expose] public section

open FirstOrder Language

namespace Montague

universe u v

/-- A composition model has a constant entity domain `E`, a world set `W`, and at each world a
first-order `L`-structure interpreting the content signature. -/
structure Model (L : Language.{u, v}) where
  /-- The entity domain is shared by all worlds. -/
  E : Type
  /-- The worlds index the interpretations. -/
  W : Type
  /-- At each world a structure interprets the signature. -/
  interp : W → L.Structure E

variable {L : Language.{u, v}}

/-- The interpretation of a constant at world `w` is the entity the structure there assigns
it. -/
def Model.const (m : Model L) (c : L.Constants) (w : m.W) : Ty.Domain m.E m.W .e :=
  (m.interp w).funMap c default

/-- The denotation `e ⇒ t` of a unary symbol at world `w` holds of the entities the structure
there relates by it. -/
def Model.pred₁ (m : Model L) (R : L.Relations 1) (w : m.W) :
    Ty.Domain m.E m.W (.e ⇒ .t) :=
  fun x ↦ (m.interp w).RelMap R (fun _ ↦ x)

/-- The denotation `e ⇒ e ⇒ t` of a binary symbol at world `w` takes the object first and the
subject second, as transitive verbs do. -/
def Model.pred₂ (m : Model L) (R : L.Relations 2) (w : m.W) :
    Ty.Domain m.E m.W (.e ⇒ .e ⇒ .t) :=
  fun y x ↦ (m.interp w).RelMap R (fun i ↦ if i = 0 then x else y)

end Montague
