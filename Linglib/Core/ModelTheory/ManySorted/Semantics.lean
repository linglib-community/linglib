module

public import Linglib.Core.ModelTheory.ManySorted.Syntax
public import Mathlib.Logic.Relator

/-!
# Realization of many-sorted terms

A term has a value in a structure, given the values of its variables, and the value of a
substituted term is the value of the term at the values of what was substituted. A relation
between the domains of two structures that every function respects [holds between the two values
of every term](##MSFirstOrder.Language.Structure.IsLogicalRel.realize).

## Main definitions

* `MSFirstOrder.Language.Term.realize`: the value of a term in a structure.
* `MSFirstOrder.Signature.Place.val`: the argument at a place.
* `MSFirstOrder.Signature.LiftRel`: a relation between two families of domains, between the
  arguments of a shape.
* `MSFirstOrder.Language.Structure.IsLogicalRel`: a relation between the domains of two
  structures that every function respects.
-/

@[expose] public section

universe u v w w' x x'

namespace MSFirstOrder

variable {S : Type u} {L : Language.{u, v} S} {α : S → Type w} {β : S → Type w'}
  {D : S → Type x}

/-- The argument at a place, among the arguments of a shape. -/
def Signature.Place.val : {σ : Signature S} → {s : S} → σ.Place s → σ.Interpret D → D s
  | _, _, .here, x => x
  | _, _, .left p, x => p.val x.1
  | _, _, .right p, x => p.val x.2

/-- A relation between two families of domains holds between the arguments of a shape when it
holds between them place by place. -/
def Signature.LiftRel {D' : S → Type x'} (R : ∀ s, D s → D' s → Prop) :
    (σ : Signature S) → σ.Interpret D → σ.Interpret D' → Prop
  | .nil, _, _ => True
  | .of s, a, b => R s a b
  | .prod σ τ, a, b => LiftRel R σ a.1 b.1 ∧ LiftRel R τ a.2 b.2

namespace Language.Term

/-- The value of a term in a structure, given the values of its variables. -/
def realize (M : L.Structure D) (ρ : ∀ {s : S}, α s → D s) :
    {σ : Signature S} → L.Term α σ → σ.Interpret D
  | _, var x => ρ x
  | _, func f r => M.funMap f (r.realize M ρ)
  | _, prod a b => (a.realize M ρ, b.realize M ρ)
  | _, nil => PUnit.unit

theorem realize_bind (M : L.Structure D) (ρ : ∀ {s : S}, β s → D s) {σ : Signature S}
    (t : L.Term α σ) (θ : ∀ {s : S}, α s → L.Term β (.of s)) :
    (t.bind θ).realize M ρ = t.realize M fun x ↦ (θ x).realize M ρ := by
  induction t with
  | var x => rfl
  | func f r ih => simp only [bind, realize, ih]
  | prod a b iha ihb => simp only [bind, realize, iha, ihb]
  | nil => rfl

theorem realize_proj (M : L.Structure D) (ρ : ∀ {s : S}, α s → D s) {σ : Signature S} {s : S}
    (t : L.Term α σ) (p : σ.Place s) : (proj p t).realize M ρ = p.val (t.realize M ρ) := by
  induction p with
  | here => rfl
  | left p ih => cases t with | prod a b => exact ih a
  | right p ih => cases t with | prod a b => exact ih b

/-- The term of argument places takes the arguments as its value. -/
theorem realize_places (M : L.Structure D) (σ : Signature S) (args : σ.Interpret D) :
    (places (L := L) σ).realize M (fun p ↦ p.val args) = args := by
  induction σ with
  | nil => rfl
  | of s => rfl
  | prod σ τ ihσ ihτ =>
    simp only [places, realize, realize_bind]
    exact Prod.ext (ihσ args.1) (ihτ args.2)

end Language.Term

variable {D' : S → Type x'} {M : L.Structure D} {M' : L.Structure D'}
  {R : ∀ s, D s → D' s → Prop}

/-- A logical relation between two structures for one language: a relation between their domains
that every function respects, taking related arguments to related values. -/
structure Language.Structure.IsLogicalRel (M : L.Structure D) (M' : L.Structure D')
    (R : ∀ s, D s → D' s → Prop) : Prop where
  /-- Each function takes related arguments to related values. -/
  funMap {σ : Signature S} {s : S} (f : L.Functions σ s) :
    Relator.LiftFun (σ.LiftRel R) (R s) (M.funMap f) (M'.funMap f)

/-- The basic lemma of logical relations: a logical relation holds between the two values of a
term whose variables have related values. -/
theorem Language.Structure.IsLogicalRel.realize (h : M.IsLogicalRel M' R)
    {ρ : ∀ {s : S}, α s → D s} {ρ' : ∀ {s : S}, α s → D' s}
    (hρ : ∀ {s : S} (a : α s), R s (ρ a) (ρ' a)) {σ : Signature S} (t : L.Term α σ) :
    σ.LiftRel R (t.realize M ρ) (t.realize M' ρ') := by
  induction t with
  | var a => exact hρ a
  | func f r ih => exact h.funMap f ih
  | prod a b iha ihb => exact ⟨iha, ihb⟩
  | nil => trivial

end MSFirstOrder