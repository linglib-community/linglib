module

public import Linglib.Core.ModelTheory.ManySorted.Syntax
public import Mathlib.Logic.Relator

/-!
# Realization of many-sorted terms

A term has a value in a structure, given the values of its variables, and the value of a
substituted term is the value of the term at the values of what was substituted. A relation
between the domains of two structures that every function respects [holds between the two values
of every term](##ManySorted.Language.Structure.IsLogicalRel.realize).

## Main definitions

* `ManySorted.Language.Term.realize`: the value of a term in a structure.
* `ManySorted.Signature.Place.val`: the argument at a place.
* `ManySorted.Signature.LiftRel`: a relation between two families of domains, between the
  arguments of a shape.
* `ManySorted.Language.Structure.IsLogicalRel`: a relation between the domains of two
  structures that every function respects.
-/

@[expose] public section

universe u v w w' x x'

namespace ManySorted

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

/-- Terms for the arguments of a shape, as one term of that shape. -/
def ofArgs : (σ : Signature S) → σ.Interpret (fun s ↦ L.Term α (.of s)) → L.Term α σ
  | .nil, _ => nil
  | .of _, t => t
  | .prod σ τ, x => prod (ofArgs σ x.1) (ofArgs τ x.2)

end Language.Term

/-- The term algebra: a symbol denotes its application to terms. -/
@[reducible] def Language.Term.structure (L : Language.{u, v} S) (α : S → Type w) :
    L.Structure fun s ↦ L.Term α (.of s) where
  funMap f x := .func f (.ofArgs _ x)

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

namespace Language.Structure.IsLogicalRel

variable {L' : Language.{u, v} S} {N : L'.Structure D} {N' : L'.Structure D'}

/-- Logical relations for two languages make one for their sum. -/
theorem sum (h : M.IsLogicalRel M' R) (h' : N.IsLogicalRel N' R) :
    (M.sum N).IsLogicalRel (M'.sum N') R where
  funMap
    | .inl f => h.funMap f
    | .inr f => h'.funMap f

/-- A relation that the unary and the binary functions respect is a logical relation between two
structures for a language of unary and binary symbols. -/
theorem mk₂ {U : S → S → Type v} {B : S → S → S → Type v}
    {unary : ∀ {a b : S}, U a b → D a → D b} {binary : ∀ {a b c : S}, B a b c → D a → D b → D c}
    {unary' : ∀ {a b : S}, U a b → D' a → D' b}
    {binary' : ∀ {a b c : S}, B a b c → D' a → D' b → D' c}
    (hu : ∀ {a b : S} (f : U a b) x x', R a x x' → R b (unary f x) (unary' f x'))
    (hb : ∀ {a b c : S} (f : B a b c) x x' y y', R a x x' → R b y y' →
      R c (binary f x y) (binary' f x' y')) :
    (Language.Structure.mk₂ (U := U) (B := B) unary binary).IsLogicalRel
      (Language.Structure.mk₂ unary' binary') R where
  funMap {σ _} f :=
    match σ, f with
    | .of _, f => fun _ _ h ↦ hu f _ _ h
    | .prod (.of _) (.of _), f => fun _ _ h ↦ hb f _ _ _ _ h.1 h.2
    | .nil, f => nomatch f
    | .prod .nil _, f => nomatch f
    | .prod (.prod _ _) _, f => nomatch f
    | .prod (.of _) .nil, f => nomatch f
    | .prod (.of _) (.prod _ _), f => nomatch f

/-- A logical relation between two structures that the new binary functions respect is one
between the two structures for the language with its binary symbols replaced. -/
theorem withBinary {B : S → S → S → Type v} {binary : ∀ {a b c : S}, B a b c → D a → D b → D c}
    {binary' : ∀ {a b c : S}, B a b c → D' a → D' b → D' c} (h : M.IsLogicalRel M' R)
    (hb : ∀ {a b c : S} (f : B a b c) x x' y y', R a x x' → R b y y' →
      R c (binary f x y) (binary' f x' y')) :
    (M.withBinary binary).IsLogicalRel (M'.withBinary binary') R where
  funMap {σ _} f :=
    match σ, f with
    | .prod (.of _) (.of _), f => fun _ _ h' ↦ hb f _ _ _ _ h'.1 h'.2
    | .nil, f => h.funMap f
    | .of _, f => h.funMap f
    | .prod .nil _, f => h.funMap f
    | .prod (.prod _ _) _, f => h.funMap f
    | .prod (.of _) .nil, f => h.funMap f
    | .prod (.of _) (.prod _ _), f => h.funMap f

variable {A : Type w} {A' : Type w'}

private theorem liftRel_app (Q : A → A' → Prop) {g : A} {g' : A'} (hg : Q g g') :
    ∀ {σ : Signature S} {p : σ.Interpret fun s ↦ A → D s} {p' : σ.Interpret fun s ↦ A' → D' s},
      σ.LiftRel (fun s v v' ↦ ∀ g g', Q g g' → R s (v g) (v' g')) p p' →
        σ.LiftRel R (Signature.Interpret.app p g) (Signature.Interpret.app p' g')
  | .nil, _, _, _ => trivial
  | .of _, _, _, h => h g g' hg
  | .prod _ _, _, _, h => ⟨liftRel_app Q hg h.1, liftRel_app Q hg h.2⟩

/-- A logical relation between two structures is one between the structures on values that
depend on a parameter, at related values of the parameters. -/
theorem pi (h : M.IsLogicalRel M' R) (Q : A → A' → Prop) :
    (M.pi A).IsLogicalRel (M'.pi A') fun s v v' ↦ ∀ g g', Q g g' → R s (v g) (v' g') where
  funMap f := fun _ _ hp _ _ hg ↦ h.funMap f (liftRel_app Q hg hp)

end Language.Structure.IsLogicalRel

end ManySorted