module

public import Linglib.Core.ModelTheory.ManySorted.Basic

/-!
# Terms of a many-sorted language

The terms of a many-sorted language over sorted variables are built from variables and function
symbols, with pairing to assemble the arguments of a symbol. A term has a shape, and a term of one
sort is a term of the shape of that sort.

## Main definitions

* `MSFirstOrder.Language.Term`: the terms over sorted variables, by shape.
* `MSFirstOrder.Language.Term.bind`: substitution of terms for variables.
* `MSFirstOrder.Signature.Place`: the argument places of a sort in a shape.
* `MSFirstOrder.Language.Term.proj`: the component of a term at an argument place.
* `MSFirstOrder.Language.Term.places`: the term whose components are the argument places.
-/

@[expose] public section

universe u v w w'

namespace MSFirstOrder

variable {S : Type u} {L : Language.{u, v} S} {α : S → Type w} {β : S → Type w'}

/-- The terms of a language over variables `α`, by the shape of what they denote. -/
inductive Language.Term (L : Language.{u, v} S) (α : S → Type w) :
    Signature S → Type (max u v w)
  /-- A variable. -/
  | var {s : S} (x : α s) : Term L α (.of s)
  /-- A function symbol applied to a term of the shape of its arguments. -/
  | func {σ : Signature S} {t : S} (f : L.Functions σ t) (r : Term L α σ) : Term L α (.of t)
  /-- A pair of terms. -/
  | prod {σ τ : Signature S} (a : Term L α σ) (b : Term L α τ) : Term L α (.prod σ τ)
  /-- The empty tuple. -/
  | nil : Term L α .nil

/-- The argument places of sort `s` in a shape. -/
inductive Signature.Place : Signature S → S → Type u
  /-- The place of a single argument. -/
  | here {s : S} : Place (.of s) s
  /-- A place in the left component. -/
  | left {σ τ : Signature S} {s : S} (p : Place σ s) : Place (.prod σ τ) s
  /-- A place in the right component. -/
  | right {σ τ : Signature S} {s : S} (p : Place τ s) : Place (.prod σ τ) s

namespace Language.Term

/-- Substitution of terms for the variables. -/
def bind : {σ : Signature S} → L.Term α σ → (∀ {s : S}, α s → L.Term β (.of s)) → L.Term β σ
  | _, var x, θ => θ x
  | _, func f r, θ => func f (r.bind θ)
  | _, prod a b, θ => prod (a.bind θ) (b.bind θ)
  | _, nil, _ => nil

/-- The component of a term at an argument place of its shape. -/
def proj : {σ : Signature S} → {s : S} → σ.Place s → L.Term α σ → L.Term α (.of s)
  | _, _, .here, t => t
  | _, _, .left p, prod a _ => proj p a
  | _, _, .right p, prod _ b => proj p b

/-- The term of a shape whose components are its argument places. -/
def places : (σ : Signature S) → L.Term σ.Place σ
  | .nil => nil
  | .of _ => var .here
  | .prod σ τ => prod ((places σ).bind fun p ↦ var (.left p))
      ((places τ).bind fun p ↦ var (.right p))

end Language.Term

end MSFirstOrder
