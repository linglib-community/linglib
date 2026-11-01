module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.List.FinRange
public import Mathlib.Logic.Relation
public import Mathlib.Order.SetNotation

import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Lattice.Bounded

/-!
# Syntax of PIP

This file defines the terms and formulas of PIP, a plural intensional presuppositional predicate
calculus. Its base is first-order predicate calculus with set abstraction, equality, the
set-theoretic relations `⊆`, `∈`, `∩`, `∅` and the cardinality predicates `SG` and `PL`. PIP adds
bracketed *local* variables `[x]`, summation `Σxφ`, formula labels `X ≡ φ` with their uses `X`,
and presuppositions `φ|ψ`. Truth is defined in `Semantics.lean` and felicity in `Felicity.lean`.

## Main definitions

* `Kind`, `Expr`, `Term`, `Formula`: the syntax, one inductive type indexed by kind.
* `Expr.vars`: the variables occurring in an expression; `Expr.locals`: its local variables;
  `Expr.subst`: substitution for a variable.
* `Expr.PresupFree`: expressions without presuppositions, decidably.
* `Expr.labels`, `Expr.defs`: the labels an expression uses and the definitions it contains;
  `DependsOn`: the use of a label in another label's definition.
* `Expr.substLabels`, `Formula.expand`, `Formula.expandSelf`: label expansion, as a bounded
  fixpoint of simultaneous substitution.
* `Expr.elim`: the translation into predicate calculus with set abstraction.

## Main statements

* `Formula.lookup_eq_none_of_mem_labels_expand`: expansion by definitions without circular
  dependencies leaves only undefined labels.

## Implementation notes

Relation symbols are indexed by the number of their non-world arguments and take a world as a
distinguished argument, where Abney and Keshet make the first argument of a predicate a world by
an assumption on models. The set-theoretic vocabulary, which ZF defines, is primitive here.

A formula is expanded before the rest of its syntax is read. `Expr.locals` and `Expr.elim` give a
label no local variables and leave it in place, where Abney and Keshet read a label through a label
assignment and leave the translation of an undefined label undefined. Substitution makes no check
for capture, which their β-reduction excludes.

## References

* [keshet-abney-2024]
* [abney-keshet-2025]
-/

@[expose] public section

namespace PIP

universe u v w

/-- The kinds of PIP expressions. -/
inductive Kind
  | term
  | formula

/-- PIP expressions. The terms are external variables, bracketed local variables `[x]`, set
abstraction `⋃{x : φ}`, summation `Σxφ`, intersection and the empty plurality. The formulas are the
constant `⊤`, predication `P_w(τ₁, …, τₙ)`, equality, inclusion, membership, the cardinality
predicates `SG` and `PL`, negation, conjunction, selective existential quantification, label
definition `X ≡ φ` and label use `X`. An expression of either kind may carry a presupposition,
`e|ψ`. The world `w` of a predication is a separate argument, where [abney-keshet-2025] (p. 11)
makes the first argument of a predicate a world by an assumption on models. -/
inductive Expr (V : Type u) (L : Type v) (P : ℕ → Type w) : Kind → Type (max u v w)
  | var (x : V) : Expr V L P .term
  | bvar (x : V) : Expr V L P .term
  | abs (x : V) (φ : Expr V L P .formula) : Expr V L P .term
  | sigma (x : V) (φ : Expr V L P .formula) : Expr V L P .term
  | inter (s t : Expr V L P .term) : Expr V L P .term
  | empty : Expr V L P .term
  | top : Expr V L P .formula
  | atom {n : ℕ} (r : P n) (w : Expr V L P .term) (ts : Fin n → Expr V L P .term) :
      Expr V L P .formula
  | eq (s t : Expr V L P .term) : Expr V L P .formula
  | subset (s t : Expr V L P .term) : Expr V L P .formula
  | mem (s t : Expr V L P .term) : Expr V L P .formula
  | sg (t : Expr V L P .term) : Expr V L P .formula
  | pl (t : Expr V L P .term) : Expr V L P .formula
  | neg (φ : Expr V L P .formula) : Expr V L P .formula
  | conj (φ ψ : Expr V L P .formula) : Expr V L P .formula
  | exists_ (x : V) (φ : Expr V L P .formula) : Expr V L P .formula
  | labelDef (X : L) (φ : Expr V L P .formula) : Expr V L P .formula
  | label (X : L) : Expr V L P .formula
  | presup {k : Kind} (e : Expr V L P k) (ψ : Expr V L P .formula) : Expr V L P k

/-- Terms. -/
abbrev Term (V : Type u) (L : Type v) (P : ℕ → Type w) := Expr V L P .term

/-- Formulas. -/
abbrev Formula (V : Type u) (L : Type v) (P : ℕ → Type w) := Expr V L P .formula

variable {V : Type u} {L : Type v} {P : ℕ → Type w}

/-- Disjunction, as `¬(¬φ ∧ ¬ψ)`. -/
def Formula.disj (φ ψ : Formula V L P) : Formula V L P := .neg (.conj (.neg φ) (.neg ψ))

/-- Implication, as `¬(φ ∧ ¬ψ)`. -/
def Formula.impl (φ ψ : Formula V L P) : Formula V L P := .neg (.conj φ (.neg ψ))

/-- Biconditional, as `(φ → ψ) ∧ (ψ → φ)`. -/
def Formula.iff_ (φ ψ : Formula V L P) : Formula V L P := (φ.impl ψ).conj (ψ.impl φ)

/-- Universal quantification, as `¬∃x¬φ`. -/
def Formula.forall_ (x : V) (φ : Formula V L P) : Formula V L P := .neg (.exists_ x (.neg φ))

/-- Overlap `some(s, t)`, as `¬(s ∩ t = ∅)`. -/
def Formula.some_ (s t : Term V L P) : Formula V L P := .neg (.eq (.inter s t) .empty)

/-- The singular summation pronoun `Σxφ | SG(Σxφ)` over the description `φ`. -/
def Term.sgPronoun (x : V) (φ : Formula V L P) : Term V L P :=
  .presup (.sigma x φ) (.sg (.sigma x φ))

/-! ### Variables and substitution -/

/-- The variables occurring in an expression, bracketed or not, bound or free. -/
def Expr.vars : ∀ {k : Kind}, Expr V L P k → Set V
  | _, .var x => {x}
  | _, .bvar x => {x}
  | _, .abs x φ => insert x φ.vars
  | _, .sigma x φ => insert x φ.vars
  | _, .inter s t => s.vars ∪ t.vars
  | _, .empty => ∅
  | _, .top => ∅
  | _, .atom _ w ts => w.vars ∪ ⋃ i, (ts i).vars
  | _, .eq s t => s.vars ∪ t.vars
  | _, .subset s t => s.vars ∪ t.vars
  | _, .mem s t => s.vars ∪ t.vars
  | _, .sg t => t.vars
  | _, .pl t => t.vars
  | _, .neg φ => φ.vars
  | _, .conj φ ψ => φ.vars ∪ ψ.vars
  | _, .exists_ x φ => insert x φ.vars
  | _, .labelDef _ φ => φ.vars
  | _, .label _ => ∅
  | _, .presup e ψ => e.vars ∪ ψ.vars

section Syntax

variable [DecidableEq V]

/-- The bracketed variables occurring free in an expression ((25)–(26) of [abney-keshet-2025]),
where set abstraction and quantification over `x` bind `[x]` and summation binds all of them. A
label use has none, where the paper's (25d) takes the local variables of the label's definition. -/
def Expr.locals : ∀ {k : Kind}, Expr V L P k → List V
  | _, .var _ => []
  | _, .bvar x => [x]
  | _, .abs x φ => φ.locals.filter (· ≠ x)
  | _, .sigma _ _ => []
  | _, .inter s t => s.locals ++ t.locals
  | _, .empty => []
  | _, .top => []
  | _, .atom _ w ts => w.locals ++ (List.finRange _).flatMap fun i => (ts i).locals
  | _, .eq s t => s.locals ++ t.locals
  | _, .subset s t => s.locals ++ t.locals
  | _, .mem s t => s.locals ++ t.locals
  | _, .sg t => t.locals
  | _, .pl t => t.locals
  | _, .neg φ => φ.locals
  | _, .conj φ ψ => φ.locals ++ ψ.locals
  | _, .exists_ x φ => φ.locals.filter (· ≠ x)
  | _, .labelDef _ _ => []
  | _, .label _ => []
  | _, .presup e ψ => e.locals ++ ψ.locals

/-- Bracket a variable, sending `x` to `[x]` and leaving other terms unchanged. -/
def Term.bracket : Term V L P → Term V L P
  | .var x => .bvar x
  | t => t

/-- Substitute `t` for the variable `x`, as in the β-reduction of `λx`. A bracketed occurrence `[x]`
becomes the bracketed substitute and binders of `x` are skipped. No capture check is made, where
the β-reduction of [abney-keshet-2025] (§2.4.6) is defined only if no free variable of `t` is
captured. -/
def Expr.subst (x : V) (t : Term V L P) : ∀ {k : Kind}, Expr V L P k → Expr V L P k
  | _, .var y => if y = x then t else .var y
  | _, .bvar y => if y = x then t.bracket else .bvar y
  | _, .abs y φ => .abs y (if y = x then φ else Expr.subst x t φ)
  | _, .sigma y φ => .sigma y (if y = x then φ else Expr.subst x t φ)
  | _, .inter s u => .inter (Expr.subst x t s) (Expr.subst x t u)
  | _, .empty => .empty
  | _, .top => .top
  | _, .atom r w ts => .atom r (Expr.subst x t w) fun i => Expr.subst x t (ts i)
  | _, .eq s u => .eq (Expr.subst x t s) (Expr.subst x t u)
  | _, .subset s u => .subset (Expr.subst x t s) (Expr.subst x t u)
  | _, .mem s u => .mem (Expr.subst x t s) (Expr.subst x t u)
  | _, .sg s => .sg (Expr.subst x t s)
  | _, .pl s => .pl (Expr.subst x t s)
  | _, .neg φ => .neg (Expr.subst x t φ)
  | _, .conj φ ψ => .conj (Expr.subst x t φ) (Expr.subst x t ψ)
  | _, .exists_ y φ => .exists_ y (if y = x then φ else Expr.subst x t φ)
  | _, .labelDef X φ => .labelDef X (Expr.subst x t φ)
  | _, .label X => .label X
  | _, .presup e ψ => .presup (Expr.subst x t e) (Expr.subst x t ψ)

end Syntax

/-! ### Expressions without presuppositions -/

/-- An expression with no presupposition operator and no label use. -/
def Expr.PresupFree : ∀ {k : Kind}, Expr V L P k → Prop
  | _, .var _ => True
  | _, .bvar _ => True
  | _, .abs _ φ => φ.PresupFree
  | _, .sigma _ φ => φ.PresupFree
  | _, .inter s t => s.PresupFree ∧ t.PresupFree
  | _, .empty => True
  | _, .top => True
  | _, .atom _ w ts => w.PresupFree ∧ ∀ i, (ts i).PresupFree
  | _, .eq s t => s.PresupFree ∧ t.PresupFree
  | _, .subset s t => s.PresupFree ∧ t.PresupFree
  | _, .mem s t => s.PresupFree ∧ t.PresupFree
  | _, .sg t => t.PresupFree
  | _, .pl t => t.PresupFree
  | _, .neg φ => φ.PresupFree
  | _, .conj φ ψ => φ.PresupFree ∧ ψ.PresupFree
  | _, .exists_ _ φ => φ.PresupFree
  | _, .labelDef _ φ => φ.PresupFree
  | _, .label _ => False
  | _, .presup _ _ => False

instance Expr.decidablePresupFree : ∀ {k : Kind} (e : Expr V L P k), Decidable e.PresupFree
  | _, .var _ | _, .bvar _ | _, .empty | _, .top => isTrue trivial
  | _, .abs _ φ | _, .sigma _ φ | _, .neg φ | _, .exists_ _ φ | _, .labelDef _ φ =>
      φ.decidablePresupFree
  | _, .sg t | _, .pl t => t.decidablePresupFree
  | _, .inter s t | _, .eq s t | _, .subset s t | _, .mem s t =>
      @instDecidableAnd _ _ s.decidablePresupFree t.decidablePresupFree
  | _, .conj φ ψ => @instDecidableAnd _ _ φ.decidablePresupFree ψ.decidablePresupFree
  | _, .atom _ w ts =>
      @instDecidableAnd _ _ w.decidablePresupFree
        (@Nat.decidableForallFin _ _ fun i => (ts i).decidablePresupFree)
  | _, .label _ | _, .presup _ _ => isFalse id

/-! ### Labels -/

/-- The labels used in an expression, inside label definitions or not. -/
def Expr.labels : ∀ {k : Kind}, Expr V L P k → Set L
  | _, .var _ => ∅
  | _, .bvar _ => ∅
  | _, .abs _ φ => φ.labels
  | _, .sigma _ φ => φ.labels
  | _, .inter s t => s.labels ∪ t.labels
  | _, .empty => ∅
  | _, .top => ∅
  | _, .atom _ w ts => w.labels ∪ ⋃ i, (ts i).labels
  | _, .eq s t => s.labels ∪ t.labels
  | _, .subset s t => s.labels ∪ t.labels
  | _, .mem s t => s.labels ∪ t.labels
  | _, .sg t => t.labels
  | _, .pl t => t.labels
  | _, .neg φ => φ.labels
  | _, .conj φ ψ => φ.labels ∪ ψ.labels
  | _, .exists_ _ φ => φ.labels
  | _, .labelDef _ φ => φ.labels
  | _, .label X => {X}
  | _, .presup e ψ => e.labels ∪ ψ.labels

/-- The label definitions occurring in an expression, the `𝒜φ` of (29) of [abney-keshet-2025]. -/
def Expr.defs : ∀ {k : Kind}, Expr V L P k → List (L × Formula V L P)
  | _, .var _ => []
  | _, .bvar _ => []
  | _, .abs _ φ => φ.defs
  | _, .sigma _ φ => φ.defs
  | _, .inter s t => s.defs ++ t.defs
  | _, .empty => []
  | _, .top => []
  | _, .atom _ w ts => w.defs ++ (List.finRange _).flatMap fun i => (ts i).defs
  | _, .eq s t => s.defs ++ t.defs
  | _, .subset s t => s.defs ++ t.defs
  | _, .mem s t => s.defs ++ t.defs
  | _, .sg t => t.defs
  | _, .pl t => t.defs
  | _, .neg φ => φ.defs
  | _, .conj φ ψ => φ.defs ++ ψ.defs
  | _, .exists_ _ φ => φ.defs
  | _, .labelDef X φ => (X, φ) :: φ.defs
  | _, .label _ => []
  | _, .presup e ψ => e.defs ++ ψ.defs

/-- Replace every label use by its definition under the label assignment `A`, leaving
undefined labels in place. -/
def Expr.substLabels (A : L → Option (Formula V L P)) : ∀ {k : Kind}, Expr V L P k → Expr V L P k
  | _, .var x => .var x
  | _, .bvar x => .bvar x
  | _, .abs x φ => .abs x (φ.substLabels A)
  | _, .sigma x φ => .sigma x (φ.substLabels A)
  | _, .inter s t => .inter (s.substLabels A) (t.substLabels A)
  | _, .empty => .empty
  | _, .top => .top
  | _, .atom r w ts => .atom r (w.substLabels A) fun i => (ts i).substLabels A
  | _, .eq s t => .eq (s.substLabels A) (t.substLabels A)
  | _, .subset s t => .subset (s.substLabels A) (t.substLabels A)
  | _, .mem s t => .mem (s.substLabels A) (t.substLabels A)
  | _, .sg t => .sg (t.substLabels A)
  | _, .pl t => .pl (t.substLabels A)
  | _, .neg φ => .neg (φ.substLabels A)
  | _, .conj φ χ => .conj (φ.substLabels A) (χ.substLabels A)
  | _, .exists_ x φ => .exists_ x (φ.substLabels A)
  | _, .labelDef X φ => .labelDef X (φ.substLabels A)
  | _, .label X => (A X).getD (.label X)
  | _, .presup e χ => .presup (e.substLabels A) (χ.substLabels A)

/-- The labels used after substitution: those of the definitions of the labels used, and the
undefined labels themselves. -/
theorem Expr.labels_substLabels (A : L → Option (Formula V L P)) {k : Kind} (e : Expr V L P k) :
    (e.substLabels A).labels = ⋃ X ∈ e.labels, (A X).elim {X} fun φ => φ.labels := by
  induction e with
  | label X => cases h : A X <;> simp [h, substLabels, labels]
  | _ =>
    simp only [substLabels, labels, Set.biUnion_union, Set.biUnion_iUnion, Set.biUnion_empty, *]

private theorem transGen_of_chain {β : Type*} {R : β → β → Prop} {p : ℕ → β} {n : ℕ}
    (hp : ∀ i < n, R (p i) (p (i + 1))) {i j : ℕ} (hij : i < j) (hjn : j ≤ n) :
    Relation.TransGen R (p i) (p j) := by
  induction j, hij using Nat.le_induction with
  | base => exact .single (hp i hjn)
  | succ j hij ih => exact .tail (ih (by omega)) (hp j (by omega))

section Expand

variable [DecidableEq L] {A : List (L × Formula V L P)}

/-- The definition of `X` in the list of definitions `A` uses the label `Y`. A cycle of this
relation is a circular definition, which makes a discourse infelicitous ((31a) of
[abney-keshet-2025]). -/
def DependsOn (A : List (L × Formula V L P)) (X Y : L) : Prop :=
  ∃ φ, A.lookup X = some φ ∧ Y ∈ φ.labels

/-- Expand a formula by a list of label definitions: as many rounds of simultaneous substitution of
each label's first definition as there are definitions. -/
def Formula.expand (A : List (L × Formula V L P)) (φ : Formula V L P) : Formula V L P :=
  (Expr.substLabels fun X => A.lookup X)^[A.length] φ

/-- Expand a formula by its own label definitions. -/
def Formula.expandSelf (φ : Formula V L P) : Formula V L P := φ.expand φ.defs

/-- A label used after `n` rounds of substitution and defined in `A` ends a chain of `n` uses of a
label in another's definition. -/
private theorem exists_dependsOn_chain {φ : Formula V L P} :
    ∀ {n : ℕ} {Y : L}, Y ∈ ((Expr.substLabels fun X => A.lookup X)^[n] φ).labels →
      A.lookup Y ≠ none → ∃ p : ℕ → L, p n = Y ∧ ∀ i < n, DependsOn A (p i) (p (i + 1))
  | 0, Y, _, _ => ⟨fun _ => Y, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, Y, hY, hYA => by
    rw [Function.iterate_succ_apply', Expr.labels_substLabels] at hY
    obtain ⟨X, hX, hXY⟩ := Set.mem_iUnion₂.1 hY
    cases hA : A.lookup X with
    | none =>
      rw [hA, Option.elim_none, Set.mem_singleton_iff] at hXY
      exact absurd (hXY ▸ hA) hYA
    | some ψ =>
      rw [hA, Option.elim_some] at hXY
      obtain ⟨p, hpX, hp⟩ := exists_dependsOn_chain hX (by simp [hA])
      refine ⟨Function.update p (n + 1) Y, by simp, fun i hi => ?_⟩
      rw [Function.update_of_ne (by omega)]
      rcases (Nat.lt_succ_iff.1 hi).lt_or_eq with hi | rfl
      · rw [Function.update_of_ne (by omega)]
        exact hp i hi
      · rw [Function.update_self, hpX]
        exact ⟨ψ, hA, hXY⟩

/-- Expansion resolves every chain of definitions that is not circular, whatever the order of the
definitions: when no label depends on itself, every label left by `Formula.expand` is undefined. -/
theorem Formula.lookup_eq_none_of_mem_labels_expand
    (hA : ∀ X, ¬ Relation.TransGen (DependsOn A) X X) {φ : Formula V L P} {Y : L}
    (hY : Y ∈ (φ.expand A).labels) : A.lookup Y = none := by
  by_contra hYA
  obtain ⟨p, hpY, hp⟩ := exists_dependsOn_chain hY hYA
  have hkeys : Set.MapsTo p (Finset.range (A.length + 1)) (A.map Prod.fst).toFinset := by
    intro i hi
    have hdef : (A.lookup (p i)).isSome := by
      rcases (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).lt_or_eq with hi | rfl
      · obtain ⟨ψ, hψ, -⟩ := hp i hi
        simp [hψ]
      · exact Option.ne_none_iff_isSome.1 (hpY ▸ hYA)
    obtain ⟨q, hq, hpq⟩ := List.lookup_isSome_iff.1 hdef
    simpa [beq_iff_eq.1 hpq] using ⟨q.2, hq⟩
  obtain ⟨i, hi, j, hj, hij, hpij⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    ((List.toFinset_card_le _).trans_lt (by simp)) hkeys
  rw [Finset.mem_range] at hi hj
  rcases hij.lt_or_gt with h | h
  · exact hA _ (hpij ▸ transGen_of_chain hp h (by omega))
  · exact hA _ (hpij.symm ▸ transGen_of_chain hp h (by omega))

end Expand

/-! ### Eliminability -/

section Elim

variable [DecidableEq V]

/-- Existential closure over a list of variables, as syntax. -/
def Formula.closeList (xs : List V) (φ : Formula V L P) : Formula V L P :=
  xs.foldr Expr.exists_ φ

/-- The translation into predicate calculus with set abstraction ((27)–(28) of
[abney-keshet-2025]). It drops brackets and presuppositions and replaces label definitions by `⊤`;
a summation `Σxφ` becomes the set abstraction over `x` of `φ` with its other local variables
existentially closed. A label use is left in place, where the paper's (27d) translates the label's
definition. -/
def Expr.elim : ∀ {k : Kind}, Expr V L P k → Expr V L P k
  | _, .var x => .var x
  | _, .bvar x => .var x
  | _, .abs x φ => .abs x φ.elim
  | _, .sigma x φ => .abs x (Formula.closeList (φ.locals.filter (· ≠ x)) φ.elim)
  | _, .inter s t => .inter s.elim t.elim
  | _, .empty => .empty
  | _, .top => .top
  | _, .atom r w ts => .atom r w.elim fun i => (ts i).elim
  | _, .eq s t => .eq s.elim t.elim
  | _, .subset s t => .subset s.elim t.elim
  | _, .mem s t => .mem s.elim t.elim
  | _, .sg t => .sg t.elim
  | _, .pl t => .pl t.elim
  | _, .neg φ => .neg φ.elim
  | _, .conj φ ψ => .conj φ.elim ψ.elim
  | _, .exists_ x φ => .exists_ x φ.elim
  | _, .labelDef _ _ => .top
  | _, .label X => .label X
  | _, .presup e _ => e.elim

end Elim

end PIP
