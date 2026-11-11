module

public import Linglib.Semantics.Composition.Effect
public import Linglib.Semantics.Composition.Basic

/-!
# Predicate abstraction

Heim and Kratzer interpret a constituent relative to an assignment, and the index a moved phrase
leaves abstracts over the value the assignment gives it. A language with predicate abstraction
is the sum of a language of rules and abstraction over each index, and from a structure for the
language it has one whose values depend on an assignment: sisters combine at one assignment, and
an abstract is a function of the value the assignment is modified to give the index. A logical
relation between two structures for the language [lifts to the
two](##ManySorted.Language.withAbstraction.isLogicalRel), and [raising a constituent of the bound
type changes nothing](##ManySorted.Language.withAbstraction.realize_raise).

## Main definitions

* `Interpreter.PredicateAbstraction`, `Interpreter.abstraction`: abstraction over an index.
* `ManySorted.Language.withAbstraction`: a language of rules with predicate abstraction.
* `Interpreter.Assignments`, `Interpreter.Assignments.total`: how assignments give indices
  values and are modified, and the total ones.
* `ManySorted.Language.withAbstraction.structure`: values relative to an assignment.
* `ManySorted.Language.withAbstraction.realize_bind`: substitution for a trace is evaluation at
  a modified assignment.

## References

* [heim-kratzer-1998]
-/

@[expose] public section

open ManySorted

namespace Interpreter

variable {B : Type} {Γ : ℕ → Ty B} {L : Language.{0, 0} (Ty B)}

/-- Predicate abstraction, for indices typed by `Γ`: over an index, a constituent of any type is
a function of the values of the index's type. -/
inductive PredicateAbstraction (Γ : ℕ → Ty B) : Ty B → Ty B → Type
  /-- Abstraction over the index `n`. -/
  | index (n : ℕ) (b : Ty B) : PredicateAbstraction Γ b (Γ n ⇒ b)

/-- Abstraction over indices typed by `Γ`, as a language over the types. -/
@[reducible] def abstraction (Γ : ℕ → Ty B) : Language.{0, 0} (Ty B) :=
  .mk₂ (PredicateAbstraction Γ) fun _ _ _ ↦ PEmpty

/-- The index a symbol of abstraction abstracts over. -/
def abstraction.index : {σ : Signature (Ty B)} → {u : Ty B} → (abstraction Γ).Functions σ u → ℕ
  | .of _, _, .index n _ => n
  | .nil, _, f => nomatch f
  | .prod .nil _, _, f => nomatch f
  | .prod (.prod _ _) _, _, f => nomatch f
  | .prod (.of _) .nil, _, f => nomatch f
  | .prod (.of _) (.prod _ _), _, f => nomatch f
  | .prod (.of _) (.of _), _, f => nomatch f

end Interpreter

/-- A language of rules with predicate abstraction over indices typed by `Γ`. -/
abbrev ManySorted.Language.withAbstraction {B : Type} (L : Language.{0, 0} (Interpreter.Ty B))
    (Γ : ℕ → Interpreter.Ty B) : Language.{0, 0} (Interpreter.Ty B) :=
  L.sum (Interpreter.abstraction Γ)

namespace Interpreter

variable {B : Type} {Γ : ℕ → Ty B}

/-- Assignments `A` of values in the domains `D` to indices typed by `Γ`: the value an assignment
gives an index, an assignment modified at an index, and the value of function type that a
function is. -/
structure Assignments (A : Type) (D : Ty B → Type) (Γ : ℕ → Ty B) where
  /-- The value an assignment gives an index. -/
  get : A → (n : ℕ) → D (Γ n)
  /-- An assignment modified to give an index a value. -/
  set : A → (n : ℕ) → D (Γ n) → A
  /-- The value of function type that a function is. -/
  lam : {a b : Ty B} → (D a → D b) → D (a ⇒ b)

variable {D : B → Type} {g : Ty B} {Γ : ℕ → Ty B}

/-- Total assignments: an assignment gives every index a value of its type, modification is at
one index, and a function is its own value of function type. -/
def Assignments.total (D : B → Type) (Γ : ℕ → Ty B) :
    Assignments (∀ n, (Γ n).Dom D) (Ty.Dom D) Γ where
  get g n := g n
  set g n v := Function.update g n v
  lam F := F

variable {A A' : Type} {D D' : Ty B → Type}

/-- Abstraction relative to assignments: the abstract over an index is the function of the value
the assignment is modified to give it. -/
@[instance_reducible] def abstraction.structure (E : Assignments A D Γ) :
    (abstraction Γ).Structure fun a ↦ A → D a :=
  .mk₂ (fun | .index n _, body => fun g ↦ E.lam fun v ↦ body (E.set g n v)) nofun

@[simp] theorem abstraction.funMap_index (E : Assignments A D Γ) (n : ℕ) (b : Ty B)
    (body : A → D b) :
    (abstraction.structure E).funMap (σ := .of b) (t := Γ n ⇒ b)
        (PredicateAbstraction.index n b) body =
      fun g ↦ E.lam fun v ↦ body (E.set g n v) := rfl

end Interpreter

namespace ManySorted.Language.withAbstraction

open Interpreter

variable {B : Type} {Γ : ℕ → Ty B} {L : Language.{0, 0} (Ty B)} {A A' : Type}
  {D D' : Ty B → Type}

/-- The values of a language with predicate abstraction relative to an assignment: the rules of
the language apply at one assignment, and the abstract over an index is the function of the
value the assignment is modified to give it. -/
@[instance_reducible] def «structure» [M : L.Structure D] (E : Assignments A D Γ) :
    (L.withAbstraction Γ).Structure fun a ↦ A → D a :=
  (M.pi A).sum (abstraction.structure E)

/-- A logical relation between two structures for a language, with a relation between their
assignments that modification and abstraction respect, is a logical relation between the two
structures relative to assignments. -/
theorem isLogicalRel [M : L.Structure D] [M' : L.Structure D'] {R : ∀ a, D a → D' a → Prop}
    (h : M.IsLogicalRel M' R) {E : Assignments A D Γ} {E' : Assignments A' D' Γ}
    (Q : A → A' → Prop)
    (hset : ∀ g g' n v v', Q g g' → R (Γ n) v v' → Q (E.set g n v) (E'.set g' n v'))
    (hlam : ∀ {a b : Ty B} (F : D a → D b) (F' : D' a → D' b),
      (∀ v v', R a v v' → R b (F v) (F' v')) → R (a ⇒ b) (E.lam F) (E'.lam F')) :
    (withAbstraction.structure (M := M) E).IsLogicalRel (withAbstraction.structure (M := M') E')
      fun a v v' ↦ ∀ g g', Q g g' → R a (v g) (v' g') :=
  (h.pi Q).sum (.mk₂
    (fun
      | .index n _ => fun _ _ hb g g' hg ↦
        hlam _ _ fun v v' hv ↦ hb _ _ (hset g g' n v v' hg hv))
    nofun)

/-! ### Substitution and raising

A derivation with another substituted for a trace has the value the derivation has at the
assignment modified to give the trace's index the value of what is substituted. Raising a
constituent of the bound type is therefore β-expansion and changes nothing: scope is taken only
where the trace is of another type than what moved. -/

section Raising

variable {W : Ty B → Type}

/-- The indices a derivation abstracts over. -/
def binders : {σ : Signature (Ty B)} → (L.withAbstraction Γ).Term W σ → Set ℕ
  | _, .var _ => ∅
  | _, .func (.inr f) r => insert (abstraction.index f) (binders r)
  | _, .func (.inl _) r => binders r
  | _, .prod a b => binders a ∪ binders b
  | _, .nil => ∅

variable [M : L.Structure D] (E : Assignments A D Γ) (ρ : ∀ {a : Ty B}, W a → A → D a)
  (θ : ∀ {a : Ty B}, W a → (L.withAbstraction Γ).Deriv W a) (n : ℕ) (val : A → D (Γ n))

/-- Substitution in a derivation is evaluation at a modified assignment: where each item's
substitute has the value the item has once the assignment gives the index `n` the value `val`,
and the derivation abstracts over no index that is `n` or that `val` depends on, the derivation
has, with the substitutes for its items, the value it has at the assignment so modified. -/
theorem realize_bind
    (hθ : ∀ {a : Ty B} (w : W a) (g : A),
      (θ w).realize (withAbstraction.structure (M := M) E) ρ g = ρ w (E.set g n (val g)))
    (hcomm : ∀ g m u v, m ≠ n → E.set (E.set g n v) m u = E.set (E.set g m u) n v)
    {σ : Signature (Ty B)} (d : (L.withAbstraction Γ).Term W σ)
    (hd : ∀ m ∈ binders d, m ≠ n ∧ ∀ g u, val (E.set g m u) = val g) (g : A) :
    Signature.Interpret.app ((d.bind θ).realize (withAbstraction.structure (M := M) E) ρ) g =
      Signature.Interpret.app (d.realize (withAbstraction.structure (M := M) E) ρ)
        (E.set g n (val g)) := by
  induction d generalizing g with
  | var w => exact hθ w g
  | nil => rfl
  | prod a b iha ihb =>
    exact Prod.ext (iha (fun k hk ↦ hd k (.inl hk)) g) (ihb (fun k hk ↦ hd k (.inr hk)) g)
  | @func σ' u f r ih =>
    cases f with
    | inl f =>
      show M.funMap f _ = M.funMap f _
      rw [ih (fun k hk ↦ hd k hk) g]
    | inr f =>
      cases σ' with
      | nil => exact nomatch f
      | prod σ₁ σ₂ => cases σ₁ <;> cases σ₂ <;> exact nomatch f
      | of a =>
        cases f with
        | index m b =>
          have hm := hd m (Set.mem_insert _ _)
          show E.lam (fun v ↦ (r.bind θ).realize _ ρ (E.set g m v)) =
            E.lam fun v ↦ r.realize _ ρ (E.set (E.set g n (val g)) m v)
          congr 1
          funext v
          have := ih (fun k hk ↦ hd k (Set.mem_insert_of_mem _ hk)) (E.set g m v)
          rw [Signature.Interpret.app_of, Signature.Interpret.app_of] at this
          rw [this, hm.2, hcomm _ _ _ _ hm.1]

/-- Raising is β-expansion: where a rule applies an abstract to a value of the bound type by
substitution, a constituent of that type combined with the abstract over the index of its
traces has the value of the derivation with the constituent in their place. -/
theorem realize_raise {b : Ty B} (ba : L.Binary (Γ n) (Γ n ⇒ b) b)
    (hβ : ∀ (v : D (Γ n)) (F : D (Γ n) → D b), M.funMap ba (v, E.lam F) = F v)
    (a : (L.withAbstraction Γ).Deriv W (Γ n))
    (hθ : ∀ {c : Ty B} (w : W c) (g : A),
      (θ w).realize (withAbstraction.structure (M := M) E) ρ g =
        ρ w (E.set g n (a.realize (withAbstraction.structure (M := M) E) ρ g)))
    (hcomm : ∀ g m u v, m ≠ n → E.set (E.set g n v) m u = E.set (E.set g m u) n v)
    (d : (L.withAbstraction Γ).Deriv W b)
    (hd : ∀ m ∈ binders d, m ≠ n ∧ ∀ g u,
      a.realize (withAbstraction.structure (M := M) E) ρ (E.set g m u) =
        a.realize (withAbstraction.structure (M := M) E) ρ g) :
    (Deriv.binary (L := L.withAbstraction Γ) (.inl ba) a
      (Deriv.unary (Language.Sum.inr (PredicateAbstraction.index n b)) d)).realize
        (withAbstraction.structure (M := M) E) ρ =
      (d.bind θ).realize (withAbstraction.structure (M := M) E) ρ := by
  funext g
  have := realize_bind E ρ θ n _ hθ hcomm d hd g
  rw [Signature.Interpret.app_of, Signature.Interpret.app_of] at this
  rw [this]
  exact hβ _ _

end Raising

end ManySorted.Language.withAbstraction
