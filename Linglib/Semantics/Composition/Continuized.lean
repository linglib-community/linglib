module

public import Linglib.Core.ModelTheory.ManySorted.Semantics
public import Mathlib.Data.Set.Image

/-!
# Continuized structures

A continuized value is a function of its context, and a context takes the value, and whatever is
still to come, to an answer. A structure for a language of rules has a continuized structure on
the same language: a rule evaluates its daughters in order, so the context of a later daughter
contains the earlier ones, and the context of an earlier daughter still awaits the later ones.
In the symmetric structure the context of each daughter contains the others. Lifting a value is
[a logical relation](##ManySorted.Language.Structure.isLogicalRel_continuized) from a structure
to either, so [a derivation over lifted items has the lift of its
value](##ManySorted.Language.Term.realize_continuized).

## Main definitions

* `Continuized`: the continuized values of a type, with `Continuized.lift`, `Continuized.map`,
  `Continuized.seq` and `Continuized.symSeq`.
* `Continuized.saturations`: the answers a context gives.
* `ManySorted.Language.Structure.continuized`, `ManySorted.Language.Structure.symContinuized`:
  the continuized structures.

## Implementation notes

A context of [barker-2022] has a type `α → R` for any `R` ending in the type of answers. Here the
arguments that `R` awaits are a single index, so a context is a family `α → ι → Ω` of answers,
and a continuized value is a function of contexts over every index type.

## References

* [barker-2022]
* [barker-2002]
-/

@[expose] public section

universe u v w x

/-- A continuized value of type `α` with answers in `Ω`: a function of its context, which takes
the value and an index `ι` for whatever is still to come to an answer. -/
def Continuized (Ω : Type v) (α : Type u) : Type (max (u + 1) v) :=
  ∀ ι : Type u, (α → ι → Ω) → ι → Ω

namespace Continuized

variable {Ω : Type v} {α β γ ι : Type u}

/-- The value that gives itself to its context. -/
def lift (a : α) : Continuized Ω α := fun _ κ ↦ κ a

/-- A continuized value under a function of values. -/
def map (h : α → β) (m : Continuized Ω α) : Continuized Ω β := fun ι κ ↦ m ι fun x ↦ κ (h x)

/-- Two continuized values in order: the context of the second contains the first, and the
context of the first awaits the second. -/
def seq (b : Continuized Ω α) (c : Continuized Ω β) : Continuized Ω (α × β) :=
  fun ι κ ↦ c ι fun y i ↦ b (β × ι) (fun x p ↦ κ (x, p.1) p.2) (y, i)

/-- Two continuized values, the context of each containing the other. -/
def symSeq (b : Continuized Ω α) (c : Continuized Ω β) : Continuized Ω (α × β) :=
  fun ι κ ↦ b ι fun x ↦ c ι fun y ↦ κ (x, y)

/-- The answer of a continuized answer in the empty context. -/
def lower (m : Continuized Ω Ω) : Ω := m PUnit (fun a _ ↦ a) ⟨⟩

@[simp] theorem map_lift (h : α → β) (a : α) : map h (lift a : Continuized Ω α) = lift (h a) := rfl

@[simp] theorem seq_lift (a : α) (b : β) :
    seq (lift a : Continuized Ω α) (lift b) = lift (a, b) := rfl

@[simp] theorem symSeq_lift (a : α) (b : β) :
    symSeq (lift a : Continuized Ω α) (lift b) = lift (a, b) := rfl

@[simp] theorem lower_lift (a : Ω) : lower (lift a) = a := rfl

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

namespace ManySorted

open Continuized

variable {S : Type w} {L : Language.{w, x} S} {D : S → Type u} {Ω : Type v}

/-- The arguments of a shape, continuized each, as continuized arguments: evaluated in order. -/
def Signature.Interpret.continuize :
    {σ : Signature S} → σ.Interpret (fun s ↦ Continuized Ω (D s)) → Continuized Ω (σ.Interpret D)
  | .nil, _ => lift PUnit.unit
  | .of _, m => m
  | .prod _ _, p => seq (continuize p.1) (continuize p.2)

/-- The arguments of a shape, continuized each, as continuized arguments: each in the context of
the others. -/
def Signature.Interpret.symContinuize :
    {σ : Signature S} → σ.Interpret (fun s ↦ Continuized Ω (D s)) → Continuized Ω (σ.Interpret D)
  | .nil, _ => lift PUnit.unit
  | .of _, m => m
  | .prod _ _, p => symSeq (symContinuize p.1) (symContinuize p.2)

namespace Language

/-- The continuized structure: a rule evaluates its arguments in order and gives its value to
the context. -/
@[instance_reducible] def Structure.continuized (Ω : Type v) (M : L.Structure D) :
    L.Structure fun s ↦ Continuized Ω (D s) where
  funMap f p := (Signature.Interpret.continuize p).map (M.funMap f)

/-- The symmetric continuized structure: a rule evaluates each argument in the context of the
others. -/
@[instance_reducible] def Structure.symContinuized (Ω : Type v) (M : L.Structure D) :
    L.Structure fun s ↦ Continuized Ω (D s) where
  funMap f p := (Signature.Interpret.symContinuize p).map (M.funMap f)

variable (M : L.Structure D)

@[simp] theorem Structure.funMap_continuized_binary {a b c : S} (f : L.Binary a b c)
    (p : Continuized Ω (D a) × Continuized Ω (D b)) :
    (M.continuized Ω).funMap (σ := .prod (.of a) (.of b)) f p =
      (seq p.1 p.2).map (M.funMap f) := rfl

@[simp] theorem Structure.funMap_continuized_unary {a b : S} (f : L.Unary a b)
    (m : Continuized Ω (D a)) :
    (M.continuized Ω).funMap (σ := .of a) f m = m.map (M.funMap f) := rfl

@[simp] theorem Structure.funMap_symContinuized_binary {a b c : S} (f : L.Binary a b c)
    (p : Continuized Ω (D a) × Continuized Ω (D b)) :
    (M.symContinuized Ω).funMap (σ := .prod (.of a) (.of b)) f p =
      (symSeq p.1 p.2).map (M.funMap f) := rfl

private theorem continuize_eq_lift :
    ∀ {σ : Signature S} {x : σ.Interpret D} {p : σ.Interpret fun s ↦ Continuized Ω (D s)},
      σ.LiftRel (fun _ a m ↦ m = lift a) x p → Signature.Interpret.continuize p = lift x
  | .nil, _, _, _ => rfl
  | .of _, _, _, h => h
  | .prod _ _, _, _, h => by
    rw [Signature.Interpret.continuize, continuize_eq_lift h.1, continuize_eq_lift h.2, seq_lift]

private theorem symContinuize_eq_lift :
    ∀ {σ : Signature S} {x : σ.Interpret D} {p : σ.Interpret fun s ↦ Continuized Ω (D s)},
      σ.LiftRel (fun _ a m ↦ m = lift a) x p → Signature.Interpret.symContinuize p = lift x
  | .nil, _, _, _ => rfl
  | .of _, _, _, h => h
  | .prod _ _, _, _, h => by
    rw [Signature.Interpret.symContinuize, symContinuize_eq_lift h.1, symContinuize_eq_lift h.2,
      symSeq_lift]

/-- Lifting is a logical relation from a structure to its continuized structure: a rule takes
lifted arguments to the lift of its value. -/
theorem Structure.isLogicalRel_continuized :
    M.IsLogicalRel (M.continuized Ω) fun _ a m ↦ m = lift a where
  funMap f := fun _ _ h ↦ by
    change (Signature.Interpret.continuize _).map (M.funMap f) = _
    rw [continuize_eq_lift h, map_lift]

/-- Lifting is a logical relation from a structure to its symmetric continuized structure. -/
theorem Structure.isLogicalRel_symContinuized :
    M.IsLogicalRel (M.symContinuized Ω) fun _ a m ↦ m = lift a where
  funMap f := fun _ _ h ↦ by
    change (Signature.Interpret.symContinuize _).map (M.funMap f) = _
    rw [symContinuize_eq_lift h, map_lift]

variable {α : S → Type*} (ρ : ∀ {s : S}, α s → D s) {s : S}

/-- A derivation whose items are lifted has, in the continuized structure, the lift of its
value. -/
theorem Term.realize_continuized (t : L.Term α (.of s)) :
    t.realize (M.continuized Ω) (fun a ↦ lift (ρ a)) = lift (t.realize M ρ) :=
  (M.isLogicalRel_continuized).realize (fun _ ↦ rfl) t

/-- A derivation whose items are lifted has, in the symmetric continuized structure, the lift of
its value. -/
theorem Term.realize_symContinuized (t : L.Term α (.of s)) :
    t.realize (M.symContinuized Ω) (fun a ↦ lift (ρ a)) = lift (t.realize M ρ) :=
  (M.isLogicalRel_symContinuized).realize (fun _ ↦ rfl) t

end Language

end ManySorted
