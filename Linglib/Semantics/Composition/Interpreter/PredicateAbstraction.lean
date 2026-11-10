module

public import Linglib.Semantics.Composition.Interpreter.Effect
public import Linglib.Semantics.Composition.Interpreter.Basic

/-!
# Predicate abstraction

Heim and Kratzer interpret a constituent relative to an assignment, and the index a moved phrase
leaves abstracts over the value the assignment gives it. A grammar with predicate abstraction has
the rules of a grammar and abstraction over each index, and from a structure for the grammar it
has one whose values depend on an assignment: sisters combine at one assignment, and an
abstract is a function of the value the assignment is modified to give the index. A logical
relation between two structures for the grammar [lifts to the
two](##Interpreter.Grammar.withAbstraction.isLogicalRel), and [raising a constituent of the bound
type changes nothing](##Interpreter.Grammar.withAbstraction.realize_raise).

## Main definitions

* `Interpreter.PredicateAbstraction`: abstraction over an index.
* `Interpreter.Grammar.withAbstraction`: a grammar with predicate abstraction.
* `Interpreter.Assignments`, `Interpreter.Assignments.total`: how assignments give indices
  values and are modified, and the total ones.
* `Interpreter.Grammar.withAbstraction.structure`: values relative to an assignment.
* `Interpreter.withAbstraction`: an interpreter that admits abstraction at an index.
* `Interpreter.Grammar.withAbstraction.realize_bind`: substitution for a trace is evaluation at
  a modified assignment.
* `Interpreter.Grammar.withAbstraction.realize_raise`: raising a constituent of the bound type
  changes nothing.

## References

* [heim-kratzer-1998]
-/

@[expose] public section

namespace Interpreter

open MSFirstOrder

variable {B : Type} {Γ : ℕ → Ty B} {G : Grammar (Ty B)}

/-- Predicate abstraction, for indices typed by `Γ`: over an index, a constituent of any type is
a function of the values of the index's type. -/
inductive PredicateAbstraction (Γ : ℕ → Ty B) : Ty B → Ty B → Type
  /-- Abstraction over the index `n`. -/
  | index (n : ℕ) (b : Ty B) : PredicateAbstraction Γ b (Γ n ⇒ b)

/-- A grammar with predicate abstraction over indices typed by `Γ`. -/
@[reducible] def Grammar.withAbstraction (G : Grammar (Ty B)) (Γ : ℕ → Ty B) :
    Grammar (Ty B) where
  Unary a b := PredicateAbstraction Γ a b ⊕ G.Unary a b
  Binary := G.Binary

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

/-- The values of a grammar with predicate abstraction relative to an assignment: the rules of
the grammar apply at one assignment, and the abstract over an index is the function of the value
the assignment is modified to give it. -/
@[instance_reducible] def Grammar.withAbstraction.structure [M : G.language.Structure D]
    (E : Assignments A D Γ) : (G.withAbstraction Γ).language.Structure fun a ↦ A → D a :=
  Grammar.structure
    (fun
      | .inl (.index n _), body => fun g ↦ E.lam fun v ↦ body (E.set g n v)
      | .inr s, v => fun g ↦ M.funMap (.unary s) (v g))
    (fun m v w g ↦ M.funMap (.binary m) (v g, w g))

@[simp] theorem Grammar.withAbstraction.funMap_index [M : G.language.Structure D]
    (E : Assignments A D Γ) (n : ℕ) (b : Ty B) (body : A → D b) :
    (Grammar.withAbstraction.structure (M := M) E).funMap (.unary (.inl (.index n b))) body =
      fun g ↦ E.lam fun v ↦ body (E.set g n v) := rfl

@[simp] theorem Grammar.withAbstraction.funMap_binary [M : G.language.Structure D]
    (E : Assignments A D Γ) {a b c : Ty B} (m : G.Binary a b c)
    (p : (A → D a) × (A → D b)) :
    (Grammar.withAbstraction.structure (M := M) E).funMap (.binary m) p =
      fun g ↦ M.funMap (.binary m) (p.1 g, p.2 g) := rfl

/-- A logical relation between two structures for a grammar, with a relation between their
assignments that modification and abstraction respect, is a logical relation between the two
structures relative to assignments. -/
theorem Grammar.withAbstraction.isLogicalRel [M : G.language.Structure D]
    [M' : G.language.Structure D'] {R : ∀ a, D a → D' a → Prop} (h : M.IsLogicalRel M' R)
    {E : Assignments A D Γ} {E' : Assignments A' D' Γ} (Q : A → A' → Prop)
    (hset : ∀ g g' n v v', Q g g' → R (Γ n) v v' → Q (E.set g n v) (E'.set g' n v'))
    (hlam : ∀ {a b : Ty B} (F : D a → D b) (F' : D' a → D' b),
      (∀ v v', R a v v' → R b (F v) (F' v')) → R (a ⇒ b) (E.lam F) (E'.lam F')) :
    (Grammar.withAbstraction.structure (M := M) E).IsLogicalRel
      (Grammar.withAbstraction.structure (M := M') E')
      fun a v v' ↦ ∀ g g', Q g g' → R a (v g) (v' g') where
  funMap
    | .unary (.inl (.index n _)) => fun _ _ hb g g' hg ↦
      hlam _ _ fun v v' hv ↦ hb _ _ (hset g g' n v v' hg hv)
    | .unary (.inr s) => fun _ _ hv g g' hg ↦ h.funMap (.unary s) (hv g g' hg)
    | .binary m => fun _ _ hp g g' hg ↦ h.funMap (.binary m) ⟨hp.1 g g' hg, hp.2 g g' hg⟩

/-! ### Substitution and raising

A derivation with another substituted for a trace has the value the derivation has at the
assignment modified to give the trace's index the value of what is substituted. Raising a
constituent of the bound type is therefore β-expansion and changes nothing: scope is taken only
where the trace is of another type than what moved. -/

section Raising

variable {W : Ty B → Type}

/-- The indices a derivation abstracts over. -/
def Grammar.withAbstraction.binders : {σ : MSFirstOrder.Signature (Ty B)} →
    (G.withAbstraction Γ).language.Term W σ → Set ℕ
  | _, .var _ => ∅
  | _, .func (.unary (.inl (.index n _))) r => insert n (binders r)
  | _, .func (.unary (.inr _)) r => binders r
  | _, .func (.binary _) r => binders r
  | _, .prod a b => binders a ∪ binders b
  | _, .nil => ∅

variable [M : G.language.Structure D] (E : Assignments A D Γ) (ρ : ∀ {a : Ty B}, W a → A → D a)
  (θ : ∀ {a : Ty B}, W a → (G.withAbstraction Γ).Deriv W a) (n : ℕ) (val : A → D (Γ n))

/-- Substitution in a derivation is evaluation at a modified assignment: where each item's
substitute has the value the item has once the assignment gives the index `n` the value `val`,
and the derivation abstracts over no index that is `n` or that `val` depends on, the derivation
has, with the substitutes for its items, the value it has at the assignment so modified. -/
theorem Grammar.withAbstraction.realize_bind
    (hθ : ∀ {a : Ty B} (w : W a) (g : A),
      (θ w).realize (Grammar.withAbstraction.structure (M := M) E) ρ g =
        ρ w (E.set g n (val g)))
    (hcomm : ∀ g m u v, m ≠ n → E.set (E.set g n v) m u = E.set (E.set g m u) n v)
    {b : Ty B} (d : (G.withAbstraction Γ).Deriv W b)
    (hd : ∀ m ∈ Grammar.withAbstraction.binders d, m ≠ n ∧ ∀ g u, val (E.set g m u) = val g)
    (g : A) :
    (d.bind θ).realize (Grammar.withAbstraction.structure (M := M) E) ρ g =
      d.realize (Grammar.withAbstraction.structure (M := M) E) ρ (E.set g n (val g)) := by
  induction d using Grammar.Deriv.induction generalizing g with
  | leaf w => exact hθ w g
  | unary s d ih =>
    cases s with
    | inl s =>
      cases s with
      | index m b =>
        have hm := hd m (Set.mem_insert _ _)
        show E.lam (fun v ↦ (d.bind θ).realize _ ρ (E.set g m v)) =
          E.lam fun v ↦ d.realize _ ρ (E.set (E.set g n (val g)) m v)
        congr 1
        funext v
        rw [ih (fun k hk ↦ hd k (Set.mem_insert_of_mem _ hk)), hm.2, hcomm _ _ _ _ hm.1]
    | inr s =>
      show M.funMap (.unary s) ((d.bind θ).realize _ ρ g) = M.funMap (.unary s) (d.realize _ ρ _)
      rw [ih fun k hk ↦ hd k (by simpa [Grammar.withAbstraction.binders] using hk)]
  | binary m d₁ d₂ ih₁ ih₂ =>
    show M.funMap (.binary m) ((d₁.bind θ).realize _ ρ g, (d₂.bind θ).realize _ ρ g) =
      M.funMap (.binary m) (d₁.realize _ ρ _, d₂.realize _ ρ _)
    rw [ih₁ (fun k hk ↦ hd k (.inl hk)), ih₂ (fun k hk ↦ hd k (.inr hk))]

/-- Raising is β-expansion: where a rule applies an abstract to a value of the bound type by
substitution, a constituent of that type combined with the abstract over the index of its
traces has the value of the derivation with the constituent in their place. -/
theorem Grammar.withAbstraction.realize_raise {b : Ty B} (ba : G.Binary (Γ n) (Γ n ⇒ b) b)
    (hβ : ∀ (v : D (Γ n)) (F : D (Γ n) → D b), M.funMap (.binary ba) (v, E.lam F) = F v)
    (a : (G.withAbstraction Γ).Deriv W (Γ n))
    (hθ : ∀ {c : Ty B} (w : W c) (g : A),
      (θ w).realize (Grammar.withAbstraction.structure (M := M) E) ρ g =
        ρ w (E.set g n (a.realize (Grammar.withAbstraction.structure (M := M) E) ρ g)))
    (hcomm : ∀ g m u v, m ≠ n → E.set (E.set g n v) m u = E.set (E.set g m u) n v)
    (d : (G.withAbstraction Γ).Deriv W b)
    (hd : ∀ m ∈ Grammar.withAbstraction.binders d, m ≠ n ∧ ∀ g u,
      a.realize (Grammar.withAbstraction.structure (M := M) E) ρ (E.set g m u) =
        a.realize (Grammar.withAbstraction.structure (M := M) E) ρ g) :
    (Grammar.Deriv.binary (G := G.withAbstraction Γ) ba a
      (Grammar.Deriv.unary (.inl (.index n b)) d)).realize
        (Grammar.withAbstraction.structure (M := M) E) ρ =
      (d.bind θ).realize (Grammar.withAbstraction.structure (M := M) E) ρ := by
  funext g
  rw [Grammar.withAbstraction.realize_bind E ρ θ n _ hθ hcomm d hd g]
  exact hβ _ _

end Raising

/-- An interpreter with predicate abstraction: an index admits abstraction over it, beside
whatever the interpreter admits. -/
def withAbstraction (I : Interpreter G Node) (Γ : ℕ → Ty B) :
    Interpreter (G.withAbstraction Γ) Node where
  unary k b :=
    (match k with
      | .index n => [⟨Γ n ⇒ b, .inl (.index n b)⟩]
      | _ => []) ++
    (I.unary k b).map fun ⟨c, s⟩ ↦ ⟨c, .inr s⟩
  binary := I.binary

end Interpreter
