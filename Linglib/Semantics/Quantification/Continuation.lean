module

public import Mathlib.Control.Monad.Cont
public import Linglib.Semantics.Quantification.Defs

/-!
# Quantifiers as continuized individuals

A quantifier holds of a scope, a set of individuals. As a function of the scope's characteristic
function it is a computation in the continuation monad at `Prop`: a generalized quantifier is a
continuized individual. The two are [equivalent](##Quantifier.toCont), and the equivalence takes
[the quantifier of an individual](##Quantifier.toCont_individual) to the unit,
[scope-taking](##Quantifier.toCont_bind) to the bind and [the image under a
function](##Quantifier.toCont_map) to the map. This is the form a quantifier has where predicates
are functions into the truth values, as in type-driven composition.

## References

* [barker-2002]
* [barwise-cooper-1981]
-/

@[expose] public section

namespace Quantifier

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
