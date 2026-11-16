/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.ModelTheory.ManySorted.Semantics
public import Mathlib.Control.Basic

/-!
# Traversal of many-sorted terms

A structure lifts along an applicative functor `A` to a structure on computations: a symbol
applies its function to the computed arguments, the effects of the earlier arguments first. This
is `ManySorted.Language.Structure.pi` when `A` is the functions from a parameter. A term is
traversed by an action on its variables, occurrence by occurrence, and
[the value of a term in the lifted structure is the computation of its values over the
traversal](##ManySorted.Language.Term.sequence_realize_applicative).

## Main definitions

* `ManySorted.Signature.Interpret.sequence`: the computation of the arguments of a shape from a
  computation of each.
* `ManySorted.Language.Structure.applicative`: the structure on computations.
* `ManySorted.Language.Term.traverse`: the traversal of a term by an action on its variables.
* `Applicative.LiftsRel`, `ManySorted.Language.Structure.IsLogicalRel.applicative`: a logical
  relation lifts to the structures on computations.
-/

@[expose] public section

universe u v v'

/-- A lifting of relations between results to relations between the computations of two
applicative functors, which returning, mapping and applying respect. -/
structure Applicative.LiftsRel {A : Type u → Type v} {A' : Type u → Type v'} [Applicative A]
    [Applicative A'] (𝓡 : ∀ {α β : Type u}, (α → β → Prop) → A α → A' β → Prop) : Prop where
  /-- Returning related values gives related computations. -/
  pure {α β : Type u} {r : α → β → Prop} : Relator.LiftFun r (𝓡 r) pure pure
  /-- Mapping related functions over related computations gives related computations. -/
  map {α β γ δ : Type u} {r : α → β → Prop} {s : γ → δ → Prop} :
    Relator.LiftFun (Relator.LiftFun r s) (Relator.LiftFun (𝓡 r) (𝓡 s)) (· <$> ·) (· <$> ·)
  /-- Applying related computations of functions to related computations gives related
  computations. -/
  seq {α β γ δ : Type u} {r : α → β → Prop} {s : γ → δ → Prop} :
    Relator.LiftFun (𝓡 (Relator.LiftFun r s)) (Relator.LiftFun (𝓡 r) (𝓡 s)) (· <*> ·) (· <*> ·)

namespace ManySorted

variable {S : Type u} {L : Language.{u, u} S} {α β D : S → Type u} {A : Type u → Type v}
  [Applicative A]

/-- The computation of the arguments of a shape from a computation of each, the effects of the
earlier arguments first. -/
def Signature.Interpret.sequence :
    (σ : Signature S) → σ.Interpret (fun s ↦ A (D s)) → A (σ.Interpret D)
  | .nil, _ => pure PUnit.unit
  | .of _, x => x
  | .prod σ τ, x => Prod.mk <$> sequence σ x.1 <*> sequence τ x.2

namespace Language

/-- The structure on the computations of an applicative functor: each symbol applies its function
to the computed arguments. -/
@[instance_reducible] def Structure.applicative (A : Type u → Type v) [Applicative A]
    (M : L.Structure D) : L.Structure fun s ↦ A (D s) where
  funMap f x := M.funMap f <$> Signature.Interpret.sequence _ x

theorem Structure.funMap_applicative (M : L.Structure D) {σ : Signature S} {t : S}
    (f : L.Functions σ t) (x : σ.Interpret fun s ↦ A (D s)) :
    (M.applicative A).funMap f x = M.funMap f <$> Signature.Interpret.sequence σ x := rfl

section LiftsRel

variable {A' : Type u → Type v'} [Applicative A'] {D' : S → Type u}
  {𝓡 : ∀ {α β : Type u}, (α → β → Prop) → A α → A' β → Prop} {R : ∀ s, D s → D' s → Prop}

private theorem liftsRel_sequence (h𝓡 : Applicative.LiftsRel 𝓡) :
    ∀ {σ : Signature S} {p : σ.Interpret fun s ↦ A (D s)} {p' : σ.Interpret fun s ↦ A' (D' s)},
      σ.LiftRel (fun s ↦ 𝓡 (R s)) p p' →
        𝓡 (σ.LiftRel R) (Signature.Interpret.sequence σ p) (Signature.Interpret.sequence σ p')
  | .nil, _, _, _ => h𝓡.pure trivial
  | .of _, _, _, h => h
  | .prod σ τ, _, _, h =>
    h𝓡.seq (r := τ.LiftRel R) (s := (σ.prod τ).LiftRel R)
      (h𝓡.map (r := σ.LiftRel R)
        (s := Relator.LiftFun (τ.LiftRel R) ((σ.prod τ).LiftRel R))
        (fun _ _ ha _ _ hb ↦ ⟨ha, hb⟩) (liftsRel_sequence h𝓡 h.1))
      (liftsRel_sequence h𝓡 h.2)

/-- A logical relation between two structures lifts to their structures on computations, through
a lifting of relations that the operations of the two functors respect. -/
theorem Structure.IsLogicalRel.applicative {M : L.Structure D} {M' : L.Structure D'}
    (h : M.IsLogicalRel M' R) (h𝓡 : Applicative.LiftsRel 𝓡) :
    (M.applicative A).IsLogicalRel (M'.applicative A') fun s ↦ 𝓡 (R s) where
  funMap f := fun _ _ hp ↦ h𝓡.map (h.funMap f) (liftsRel_sequence h𝓡 hp)

end LiftsRel

namespace Term

/-- The traversal of a term by an action on its variables, one occurrence after another. -/
def traverse (g : ∀ {s : S}, α s → A (β s)) : {σ : Signature S} → L.Term α σ → A (L.Term β σ)
  | _, var x => var <$> g x
  | _, func f r => func f <$> traverse g r
  | _, prod a b => prod <$> traverse g a <*> traverse g b
  | _, nil => pure nil

variable [LawfulApplicative A]

/-- The value of a term in the structure on computations, where each variable is the computation
of a value of some variable, is the computation of the values of the terms it traverses. -/
theorem sequence_realize_applicative (M : L.Structure D) (ρ : ∀ {s : S}, β s → D s)
    (g : ∀ {s : S}, α s → A (β s)) {σ : Signature S} (t : L.Term α σ) :
    Signature.Interpret.sequence σ (t.realize (M.applicative A) fun x ↦ ρ <$> g x) =
      (fun t' : L.Term β σ ↦ t'.realize M ρ) <$> t.traverse g := by
  induction t with
  | var x => simp only [realize, traverse, Signature.Interpret.sequence, Functor.map_map]
  | func f r ih =>
    simp only [realize, traverse, Signature.Interpret.sequence, Structure.funMap_applicative, ih,
      Functor.map_map]
  | prod a b iha ihb =>
    simp only [realize, traverse, Signature.Interpret.sequence, iha, ihb, Functor.map_map,
      map_seq, seq_map_assoc]
    rfl
  | nil => simp only [realize, traverse, Signature.Interpret.sequence, map_pure]

/-- The value of a term of one sort in the structure on computations is the computation of the
values of the terms it traverses. -/
theorem realize_applicative (M : L.Structure D) (ρ : ∀ {s : S}, β s → D s)
    (g : ∀ {s : S}, α s → A (β s)) {s : S} (t : L.Term α (.of s)) :
    t.realize (M.applicative A) (fun x ↦ ρ <$> g x) =
      (fun t' : L.Term β (.of s) ↦ t'.realize M ρ) <$> t.traverse g :=
  sequence_realize_applicative M ρ g t

end Term

end Language

end ManySorted
