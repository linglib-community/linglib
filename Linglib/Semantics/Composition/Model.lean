module

public import Linglib.Semantics.Composition.Ty
public import Mathlib.ModelTheory.Basic

/-!
# Model-theoretic semantics for type-driven composition

A composition model is a mathlib first-order structure on one entity domain at each world of a
world set. The symbols of the signature denote what the structure gives them, read off through
`Structure.funMap` and `Structure.RelMap` as DRT reads off the truth of atomic conditions
(`Semantics/Dynamic/DRS/`), and world dependence stays in the `.intens` types. The words of a
first-order fragment translate to these symbols (`Composition/Reduction.lean`).

## Main definitions

* `Model`: an entity domain `E`, worlds `W`, and a structure `interp w` at each world.
* `Model.const`, `Model.pred₁`, `Model.pred₂`: the denotations of a constant and of unary
  and binary relation symbols at a world.

## Implementation notes

`interp : W → L.Structure E` carries structures as terms rather than instances, since a
world-indexed family of structures on one carrier cannot be instance-based; formulas are
realized at a world by `Formula.RealizeAt m.interp w`. The concrete toy model of
`Studies/HeimKratzer1998` follows mathlib's concrete-language idiom.

## References

* [heim-kratzer-1998]
-/

@[expose] public section

open FirstOrder Language
open Montague

namespace HeimKratzer

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

end HeimKratzer
