module

public import Mathlib.Control.Monad.Cont
public import Mathlib.Data.Part
public import Mathlib.Data.Set.Functor
public import Mathlib.Data.Set.Lattice.Image
public import Linglib.Semantics.Alternatives.WithAlternatives

/-!
# Types with effects

Bumford and Charlow type an expression whose meaning exceeds what its position expects as a
computation with an effect: a pronoun reads a referent, a definite description may fail, an
appositive stores a comment, a *wh*-phrase returns one of several values, a focused phrase
evokes alternatives to its value, and a quantifier consults its continuation. A computation type
is an effect applied to the type of its result. Each effect is a functor, and each but storing at
a type with no way of merging two stored contents is applicative and a monad; storing is left
adjoint to reading, and
[reading distributes over functions](##Interpreter.Eff.eject).

## Main definitions

* `Interpreter.Ty`, `Interpreter.Eff`: the types over a set of base sorts, and the effects.
* `Interpreter.Ty.Dom`, `Interpreter.Eff.Obj`: the domain of a type and the carrier of an effect,
  given the domains of the base sorts.
* `Interpreter.Eff.IsApplicative`: the effects with a unit and an application.
* `Interpreter.Eff.map`, `Interpreter.Eff.pure`, `Interpreter.Eff.seq`, `Interpreter.Eff.join`:
  the operations of an effect.
* `Interpreter.Ty.size`, `Interpreter.Eff.size`: the size of a type and of an effect.
* `Interpreter.Eff.counit`, `Interpreter.Eff.eject`, `Interpreter.Eff.lower`: the co-unit of
  storing and reading, the ejection of reading from a function, and the lowering of a
  continuation at its own result type.

## Implementation notes

Truth values are a type of their own and not a base sort, since predicate modification, lowering
and the merging of stored truth values name them. The carriers are the standard ones, `Set`,
functions, products, `Cont`, `Part` and `WithAlternatives`, and the operations are theirs.
Storing is applicative only at the truth values, merged by conjunction, as in the book's
interpreter. State and dynamic state are not effects here: the book derives them from storing and
reading.

## References

* [bumford-charlow-2026]
-/

@[expose] public section

namespace Interpreter

mutual

/-- The types over base sorts `B`: truth values, a base sort, functions, and computations with an
effect. -/
inductive Ty (B : Type) where
  /-- Truth values. -/
  | t
  /-- A base sort. -/
  | base (b : B)
  /-- Functions. -/
  | fn (a b : Ty B)
  /-- Computations with effect `f` and result of type `a`. -/
  | comp (f : Eff B) (a : Ty B)
  deriving DecidableEq, Repr

/-- The effects. -/
inductive Eff (B : Type) where
  /-- Indeterminacy: a set of alternative results. -/
  | S
  /-- Reading a datum of type `i`. -/
  | R (i : Ty B)
  /-- Storing a datum of type `o`. -/
  | W (o : Ty B)
  /-- Quantifying over continuations with result type `r`. -/
  | C (r : Ty B)
  /-- Partiality: a result that may be undefined. -/
  | M
  /-- Alternatives: a result with the alternatives to it, as a focused phrase evokes. -/
  | F
  deriving DecidableEq, Repr

end

@[inherit_doc] scoped infixr:25 " ⇒ " => Ty.fn

variable {B : Type}

mutual

/-- The domain of a type, given the domains of the base sorts. -/
abbrev Ty.Dom (D : B → Type) (ty : Ty B) : Type :=
  match ty with
  | .t => Prop
  | .base b => D b
  | .fn a b => Ty.Dom D a → Ty.Dom D b
  | .comp f a => Eff.Obj D f (Ty.Dom D a)

/-- The carrier of an effect: a set of alternatives, a function of the datum read, a pair with
the datum stored, a function of the continuation, a partial value, or a value with its
alternatives. -/
abbrev Eff.Obj (D : B → Type) (f : Eff B) (α : Type) : Type :=
  match f with
  | .S => Set α
  | .R i => Ty.Dom D i → α
  | .W o => α × Ty.Dom D o
  | .C r => Cont (Ty.Dom D r) α
  | .M => Part α
  | .F => WithAlternatives α

end

namespace Eff

variable {D : B → Type} {α β : Type}

/-- The effects with a unit and an application: all but storing at a type other than the truth
values, whose stored contents cannot be merged. -/
def IsApplicative : Eff B → Prop
  | .W o => o = .t
  | _ => True

instance [DecidableEq B] : DecidablePred (IsApplicative (B := B))
  | .W o => inferInstanceAs (Decidable (o = .t))
  | .S | .R _ | .C _ | .M | .F => isTrue trivial

/-- An effect's map. -/
def map : (f : Eff B) → (α → β) → Obj D f α → Obj D f β
  | .S, g, x => g '' x
  | .R _, g, x => fun i ↦ g (x i)
  | .W _, g, x => (g x.1, x.2)
  | .C _, g, x => fun c ↦ x fun a ↦ c (g a)
  | .M, g, x => x.map g
  | .F, g, x => Functor.map (f := WithAlternatives) g x

/-- An applicative effect's unit. -/
def pure : (f : Eff B) → f.IsApplicative → α → Obj D f α
  | .S, _, a => {a}
  | .R _, _, a => fun _ ↦ a
  | .W _, h, a => (a, cast (by rw [h]) True)
  | .C _, _, a => fun c ↦ c a
  | .M, _, a => Part.some a
  | .F, _, a => .unfeatured a

/-- An applicative effect's application of a computed function to a computed argument, the
effects of the function first. -/
def seq : (f : Eff B) → f.IsApplicative → Obj D f (α → β) → Obj D f α →
    Obj D f β
  | .S, _, g, x => Set.seq g x
  | .R _, _, g, x => fun i ↦ g i (x i)
  | .W o, h, g, x => (g.1 x.1, by subst h; exact g.2 ∧ x.2)
  | .C _, _, g, x => fun c ↦ g fun k ↦ x fun a ↦ c (k a)
  | .M, _, g, x => g.bind fun k ↦ x.map k
  | .F, _, g, x => Seq.seq (f := WithAlternatives) g fun _ ↦ x

/-- A monadic effect's flattening of a computation of a computation. -/
def join : (f : Eff B) → f.IsApplicative → Obj D f (Obj D f α) → Obj D f α
  | .S, _, x => ⋃₀ x
  | .R _, _, x => fun i ↦ x i i
  | .W o, h, x => (x.1.1, by subst h; exact x.2 ∧ x.1.2)
  | .C _, _, x => fun c ↦ x fun m ↦ m c
  | .M, _, x => x.bind id
  | .F, _, x => Bind.bind (m := WithAlternatives) x id

/-- The co-unit of storing and reading: the stored datum is given to the reader. -/
def counit {i : Ty B} (x : Obj D (.W i) (Obj D (.R i) α)) : α := x.1 x.2

/-- Reading distributes over functions: a function into a reader is a reader of functions. -/
def eject {i : Ty B} (k : α → Obj D (.R i) β) : Obj D (.R i) (α → β) :=
  fun j a ↦ k a j

/-- A continuation at its own result type lowers to its value at the identity. -/
def lower {r : Ty B} (m : Obj D (.C r) (Ty.Dom D r)) : Ty.Dom D r := m id

@[simp] theorem map_id (f : Eff B) (x : Obj D f α) : map f id x = x := by
  cases f with
  | M => exact Part.map_id' (fun _ ↦ rfl) x
  | F => exact id_map (f := WithAlternatives) x
  | _ => simp [map]

theorem map_map (f : Eff B) (g : α → β) {γ : Type} (h : β → γ) (x : Obj D f α) :
    map f h (map f g x) = map f (h ∘ g) x := by
  cases f with
  | S => simp [map, Set.image_image]
  | M => simp [map, Part.map_map]
  | F => exact (comp_map (f := WithAlternatives) g h x).symm
  | _ => rfl

end Eff

mutual

/-- The size of a type. -/
def Ty.size : Ty B → ℕ
  | .t | .base _ => 1
  | .fn a b => a.size + b.size + 1
  | .comp f a => f.size + a.size + 1

/-- The size of an effect. -/
def Eff.size : Eff B → ℕ
  | .S | .M | .F => 1
  | .R i | .W i | .C i => i.size + 1

end

end Interpreter
