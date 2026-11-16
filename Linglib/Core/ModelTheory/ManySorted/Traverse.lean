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
* `ManySorted.Language.Structure.isLogicalRel_applicative`: returning a value is a logical
  relation from a structure to its structure on computations.
-/

@[expose] public section

universe u v

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

private theorem sequence_eq_pure
    (hmap : ∀ {γ δ : Type u} (f : γ → δ) (a : γ), f <$> (pure a : A γ) = pure (f a))
    (hseq : ∀ {γ δ : Type u} (f : γ → δ) (a : γ), (pure f : A (γ → δ)) <*> pure a = pure (f a)) :
    ∀ {σ : Signature S} {x : σ.Interpret D} {p : σ.Interpret fun s ↦ A (D s)},
      σ.LiftRel (D := D) (D' := fun s ↦ A (D s)) (fun _ a m ↦ m = pure a) x p →
        Signature.Interpret.sequence σ p = pure x
  | .nil, _, _, _ => rfl
  | .of _, _, _, h => h
  | .prod _ _, _, _, h => by
    rw [Signature.Interpret.sequence, sequence_eq_pure hmap hseq h.1,
      sequence_eq_pure hmap hseq h.2, hmap, hseq]

/-- The computation that only returns a value is a logical relation from a structure to its
structure on computations, where mapping and applying such computations returns the value mapped
and applied, as in a lawful applicative functor: a symbol takes them to the one that returns its
value. -/
theorem Structure.isLogicalRel_applicative (M : L.Structure D)
    (hmap : ∀ {γ δ : Type u} (f : γ → δ) (a : γ), f <$> (pure a : A γ) = pure (f a))
    (hseq : ∀ {γ δ : Type u} (f : γ → δ) (a : γ), (pure f : A (γ → δ)) <*> pure a = pure (f a)) :
    M.IsLogicalRel (M.applicative A) fun _ a m ↦ m = pure a where
  funMap f := fun _ _ h ↦ by
    change (M.applicative A).funMap f _ = pure _
    rw [Structure.funMap_applicative, sequence_eq_pure hmap hseq h, hmap]

namespace Term

/-- A term whose variables only return values has, in the structure on computations, the
computation that returns its value. -/
theorem realize_applicative_pure (M : L.Structure D)
    (hmap : ∀ {γ δ : Type u} (f : γ → δ) (a : γ), f <$> (pure a : A γ) = pure (f a))
    (hseq : ∀ {γ δ : Type u} (f : γ → δ) (a : γ), (pure f : A (γ → δ)) <*> pure a = pure (f a))
    (ρ : ∀ {s : S}, α s → D s) {s : S} (t : L.Term α (.of s)) :
    t.realize (M.applicative A) (fun x ↦ pure (ρ x)) = pure (t.realize M ρ) :=
  (M.isLogicalRel_applicative hmap hseq).realize (fun _ ↦ rfl) t

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
