module

public import Mathlib.Control.Monad.Cont
public import Linglib.Semantics.Quantifier.Defs

/-!
# Quantifiers taking scope: the continuation monad

A quantifier applies to its scope, the set obtained by abstracting over one position in the rest
of the sentence. This file defines the operations by which quantifiers take scope over one
another:

* `Q.map f` is the image of `Q` under `f`: it holds of `B` if `Q` holds of `f ⁻¹' B`;
* `Q.bind m` puts the quantifiers `m a` in the scope of `Q`: it holds of `B` if `Q` holds of the
  set of `a` such that `m a` holds of `B`;
* `Q₁.curry Q₂` is the quantifier over pairs in which `Q₁` takes scope over `Q₂`.

With the individual of an entity as the unit, these are the operations of a monad. It is the
continuation monad at `Prop`: a quantifier, read as a function of the characteristic function of
its scope, is a computation `Cont Prop α`, and under this equivalence the individual of an entity
is `pure`, `bind` is `>>=` and `map` is `<$>`.

## Implementation notes

`map`, `bind` and `curry` follow `Filter.map`, `Filter.bind` and `Filter.curry`.

## References

* [barker-2002]
* [barwise-cooper-1981]
-/

@[expose] public section

namespace Quantifier

/-! ### Scope-taking -/

section Scope

variable {α β γ : Type*}

/-- The image of a quantifier under a function, which holds of the sets whose preimage it holds
of. -/
def map (f : α → β) (Q : Quantifier α) : Quantifier β := fun B ↦ Q (f ⁻¹' B)

/-- `Q.bind m` takes scope over `m`: it holds of `B` when `Q` holds of the `a` whose quantifier
`m a` holds of `B`. -/
def bind (Q : Quantifier α) (m : α → Quantifier β) : Quantifier β := fun B ↦ Q {a | m a B}

/-- The quantifier over pairs on which `Q₁` takes scope over `Q₂`, the iteration `Q₁x Q₂y`. -/
def curry (Q₁ : Quantifier α) (Q₂ : Quantifier β) : Quantifier (α × β) :=
  Q₁.bind fun a ↦ Q₂.map (a, ·)

theorem map_apply (f : α → β) (Q : Quantifier α) (B : Set β) : Q.map f B ↔ Q (f ⁻¹' B) := .rfl

theorem bind_apply (Q : Quantifier α) (m : α → Quantifier β) (B : Set β) :
    Q.bind m B ↔ Q {a | m a B} := .rfl

theorem curry_apply (Q₁ : Quantifier α) (Q₂ : Quantifier β) (R : Set (α × β)) :
    Q₁.curry Q₂ R ↔ Q₁ {a | Q₂ {b | (a, b) ∈ R}} := .rfl

@[simp] theorem map_id (Q : Quantifier α) : Q.map id = Q := rfl

theorem map_map (f : α → β) (g : β → γ) (Q : Quantifier α) : (Q.map f).map g = Q.map (g ∘ f) :=
  rfl

@[simp] theorem map_individual (f : α → β) (a : α) : (individual a).map f = individual (f a) :=
  rfl

@[simp] theorem individual_bind (a : α) (m : α → Quantifier β) : (individual a).bind m = m a :=
  rfl

@[simp] theorem bind_individual (Q : Quantifier α) : Q.bind individual = Q := rfl

theorem bind_assoc (Q : Quantifier α) (m : α → Quantifier β) (n : β → Quantifier γ) :
    (Q.bind m).bind n = Q.bind fun a ↦ (m a).bind n := rfl

theorem bind_individual_comp (Q : Quantifier α) (f : α → β) :
    (Q.bind fun a ↦ individual (f a)) = Q.map f := rfl

/-- An individual takes no scope: its two orders with any quantifier agree. -/
theorem map_swap_individual_curry (a : α) (Q : Quantifier β) :
    ((individual a).curry Q).map Prod.swap = Q.curry (individual a) := rfl

theorem bind_mono {Q : Quantifier α} (hQ : Monotone Q) {m m' : α → Quantifier β}
    (h : ∀ a, m a ≤ m' a) : Q.bind m ≤ Q.bind m' :=
  fun B ↦ hQ fun a ↦ h a B

end Scope

/-! ### The continuation monad -/

universe u

variable {α β : Type u}

/-- A quantifier as a computation in the continuation monad at `Prop`: it applies to a predicate
as it does to the set of what satisfies the predicate. -/
def toCont : Quantifier α ≃ Cont Prop α where
  toFun Q := fun k ↦ Q {x | k x}
  invFun m := fun B ↦ m (· ∈ B)
  left_inv _ := rfl
  right_inv _ := rfl

theorem toCont_run (Q : Quantifier α) (k : α → Prop) : (toCont Q).run k ↔ Q {x | k x} := .rfl

theorem toCont_symm_apply (m : Cont Prop α) (B : Set α) : toCont.symm m B ↔ m.run (· ∈ B) := .rfl

/-- The quantifier of an individual is the continuized individual. -/
@[simp] theorem toCont_individual (a : α) : toCont (individual a) = pure a := rfl

/-- Scope-taking is the bind of the continuation monad. -/
theorem toCont_bind (Q : Quantifier α) (m : α → Quantifier β) :
    toCont (Q.bind m) = toCont Q >>= fun a ↦ toCont (m a) := rfl

/-- The image of a quantifier under a function is the map of the continuation monad. -/
theorem toCont_map (f : α → β) (Q : Quantifier α) : toCont (Q.map f) = f <$> toCont Q := rfl

end Quantifier
