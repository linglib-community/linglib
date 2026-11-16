module

public import Linglib.Core.ModelTheory.ManySorted.Traverse
public import Mathlib.Data.Set.Image

/-!
# Continuized values

A continuized value is a function of its context, and a context takes the value, and whatever is
still to come, to an answer. Continuized values are computations: applying one to another
evaluates the function first, so the context of the argument contains the function and the
context of the function still awaits the argument. The structure on these computations of a
structure for a language of rules, `ManySorted.Language.Structure.applicative`, is the
continuized grammar, and a derivation over lifted items [has the lift of its
value](##Continuized.realize_applicative_lift). Applying in the context of each other is a second
application, `Continuized.symmetric`.

## Main definitions

* `Continuized`: the continuized values of a type, with `Continuized.lift` and `Continuized.map`,
  computations by evaluation in order.
* `Continuized.symmetric`: the computations in which each of two values is in the context of the
  other.
* `Continuized.saturations`: the answers a context gives.

## Implementation notes

A context of [barker-2022] has a type `α → R` for any `R` ending in the type of answers. Here the
arguments that `R` awaits are a single index, so a context is a family `α → ι → Ω` of answers,
and a continuized value is a function of contexts over every index type. Evaluation in order is
not a lawful applicative functor: a value may inspect the whole of its context, as a
presupposition trigger does, and then associating an application differently changes the index
it sees.

## References

* [barker-2022]
* [barker-2002]
-/

@[expose] public section

universe u v w

/-- A continuized value of type `α` with answers in `Ω`: a function of its context, which takes
the value and an index `ι` for whatever is still to come to an answer. -/
def Continuized (Ω : Type v) (α : Type u) : Type (max (u + 1) v) :=
  ∀ ι : Type u, (α → ι → Ω) → ι → Ω

namespace Continuized

variable {Ω : Type v} {α β : Type u}

/-- The value that gives itself to its context. -/
def lift (a : α) : Continuized Ω α := fun _ κ ↦ κ a

/-- A continuized value under a function of values. -/
def map (h : α → β) (m : Continuized Ω α) : Continuized Ω β := fun ι κ ↦ m ι fun x ↦ κ (h x)

/-- Evaluation in order: the context of the argument contains the function, and the context of
the function awaits the argument. -/
instance : Applicative (Continuized.{u, v} Ω) where
  pure := lift
  map := map
  seq f x := fun ι κ ↦ x () ι fun a i ↦ f (_ × ι) (fun g p ↦ κ (g p.1) p.2) (a, i)

/-- Evaluation of a function and its argument each in the context of the other. -/
@[reducible] def symmetric : Applicative (Continuized.{u, v} Ω) where
  pure := lift
  map := map
  seq f x := fun ι κ ↦ f ι fun g ↦ x () ι fun a ↦ κ (g a)

/-- The answer of a continuized answer in the empty context. -/
def lower (m : Continuized Ω Ω) : Ω := m PUnit (fun a _ ↦ a) ⟨⟩

@[simp] theorem map_lift (h : α → β) (a : α) : map h (lift a : Continuized Ω α) = lift (h a) := rfl

@[simp] theorem lower_lift (a : Ω) : lower (lift a) = a := rfl

theorem pure_eq_lift (a : α) : (pure a : Continuized.{u, v} Ω α) = lift a := rfl

open ManySorted ManySorted.Language in
/-- A derivation whose items are lifted has, in the structure on continuized values, the lift of
its value. -/
theorem realize_applicative_lift {S : Type u} {L : Language.{u, u} S} {D γ : S → Type u}
    (M : L.Structure D) (ρ : ∀ {s : S}, γ s → D s) {s : S} (t : L.Term γ (.of s)) :
    t.realize (M.applicative (Continuized.{u, v} Ω)) (fun x ↦ lift (ρ x)) = lift (t.realize M ρ) :=
  Term.realize_applicative_pure M (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) ρ t

open ManySorted ManySorted.Language in
/-- A derivation whose items are lifted has, evaluated symmetrically, the lift of its value. -/
theorem realize_applicative_symmetric_lift {S : Type u} {L : Language.{u, u} S}
    {D γ : S → Type u} (M : L.Structure D) (ρ : ∀ {s : S}, γ s → D s) {s : S}
    (t : L.Term γ (.of s)) :
    t.realize (@Structure.applicative _ _ _ (Continuized.{u, v} Ω) symmetric M)
        (fun x ↦ lift (ρ x)) = lift (t.realize M ρ) :=
  @Term.realize_applicative_pure _ _ _ _ (Continuized.{u, v} Ω) symmetric M (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) ρ _ t

/-- The answers a context gives, over its values and whatever is still to come. -/
def saturations {α ι : Type*} (κ : α → ι → Ω) : Set Ω := Set.range fun p : α × ι ↦ κ p.1 p.2

section Saturations

variable {α ι δ ε : Type*} {κ : α → ι → Ω} {κ' : δ → ε → Ω}

theorem mem_saturations {p : Ω} : p ∈ saturations κ ↔ ∃ a i, κ a i = p :=
  ⟨fun ⟨⟨a, i⟩, h⟩ ↦ ⟨a, i, h⟩, fun ⟨a, i, h⟩ ↦ ⟨(a, i), h⟩⟩

theorem saturations_subset (h : ∀ a i, ∃ d e, κ' d e = κ a i) :
    saturations κ ⊆ saturations κ' := by
  rintro _ ⟨⟨a, i⟩, rfl⟩
  obtain ⟨d, e, h⟩ := h a i
  exact ⟨(d, e), h⟩

end Saturations

end Continuized
