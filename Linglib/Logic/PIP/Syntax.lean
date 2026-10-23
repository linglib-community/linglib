module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.List.FinRange

/-!
# Syntax of PIP

This file defines the terms and formulas of PIP, a plural intensional presuppositional predicate
calculus. Its base is first-order predicate calculus with set abstraction, equality, the
set-theoretic relations `⊆`, `∈`, `∩`, `∅` and the cardinality predicates `SG` and `PL`. PIP adds
bracketed *local* variables `[x]`, summation `Σxφ`, formula labels `X ≡ φ` with their uses `X`,
and presuppositions `φ|ψ`. Relation symbols are indexed by arity and take a world as a
distinguished argument. Truth is defined in `Semantics.lean` and felicity in `Felicity.lean`.

## Main definitions

* `Kind`, `Expr`, `Term`, `Formula`: the syntax, one inductive type indexed by kind.
* `Formula.disj`, `Formula.impl`, `Formula.iff_`, `Formula.forall_`, `Formula.some_`: the defined
  connectives; `Term.sgPronoun`: a singular summation pronoun.
* `Expr.locals`: the local variables; `Expr.subst`: substitution for a variable.
* `Expr.PresupFree`: expressions without presuppositions, decidably.
* `Expr.substLabels`, `Expr.defs`, `assignment`, `Formula.expand`, `Formula.expandSelf`: label
  assignment and expansion, as a bounded fixpoint of simultaneous substitution.
* `Formula.closeList`, `Expr.elim`: the translation eliminating the PIP constructs into predicate
  calculus with set abstraction.

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

/-- PIP expressions. Terms: external variables, bracketed local variables `[x]`,
set abstraction `⋃{x : φ}`, summation `Σxφ`, intersection and the empty
plurality. Formulas: the constant `⊤`, predication `P_w(τ₁, …, τₙ)`, equality,
inclusion, membership, the cardinality predicates `SG` and `PL`, negation,
conjunction, selective existential quantification, label definition `X ≡ φ`
and label use `X`. An expression of either kind may carry a presupposition,
`e|ψ`. -/
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

/-- `Σxφ | SG(Σxφ)`: a singular summation pronoun over the description `φ`. -/
def Term.sgPronoun (x : V) (φ : Formula V L P) : Term V L P :=
  .presup (.sigma x φ) (.sg (.sigma x φ))

/-! ### Local variables and substitution -/

section Syntax

variable [DecidableEq V]

/-- The bracketed variables occurring free in an expression: set abstraction and quantification
over `x` bind `[x]`, and summation binds all of them. -/
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

/-- Bracket a variable: `[x]` for `x`; other terms are unchanged. -/
def Term.bracket : Term V L P → Term V L P
  | .var x => .bvar x
  | t => t

/-- Substitute `t` for the variable `x`, the β-reduction of `λx`: a bracketed
occurrence `[x]` becomes the bracketed substitute, binders of `x` are skipped,
and no capture check is made. -/
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
  | _, .atom _ w ts => w.PresupFree ∧ ∀ i ∈ List.finRange _, (ts i).PresupFree
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

/-- Decidability of `Expr.PresupFree`. -/
def Expr.decPresupFree : ∀ {k : Kind} (e : Expr V L P k), Decidable e.PresupFree
  | _, .var _ => isTrue trivial
  | _, .bvar _ => isTrue trivial
  | _, .abs _ φ => φ.decPresupFree
  | _, .sigma _ φ => φ.decPresupFree
  | _, .inter s t => @instDecidableAnd _ _ s.decPresupFree t.decPresupFree
  | _, .empty => isTrue trivial
  | _, .top => isTrue trivial
  | _, .atom _ w ts =>
      @instDecidableAnd _ _ w.decPresupFree
        (@List.decidableBAll _ _ (fun i => (ts i).decPresupFree) _)
  | _, .eq s t => @instDecidableAnd _ _ s.decPresupFree t.decPresupFree
  | _, .subset s t => @instDecidableAnd _ _ s.decPresupFree t.decPresupFree
  | _, .mem s t => @instDecidableAnd _ _ s.decPresupFree t.decPresupFree
  | _, .sg t => t.decPresupFree
  | _, .pl t => t.decPresupFree
  | _, .neg φ => φ.decPresupFree
  | _, .conj φ ψ => @instDecidableAnd _ _ φ.decPresupFree ψ.decPresupFree
  | _, .exists_ _ φ => φ.decPresupFree
  | _, .labelDef _ φ => φ.decPresupFree
  | _, .label _ => isFalse id
  | _, .presup _ _ => isFalse id

instance {k : Kind} (e : Expr V L P k) : Decidable e.PresupFree := e.decPresupFree

/-! ### Labels -/

section Labels

variable [DecidableEq L]

/-- Replace every label use by its definition under the assignment `A`, leaving
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

/-- The label definitions occurring in an expression. -/
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

/-- The label assignment determined by a list of definitions: the first
definition of each label. -/
def assignment : List (L × Formula V L P) → L → Option (Formula V L P)
  | [], _ => none
  | (Y, ψ) :: A, X => if Y = X then some ψ else assignment A X

/-- Expand a formula by a list of label definitions: one round of simultaneous
substitution per definition, which resolves every non-circular chain of
definitions whatever their order. -/
def Formula.expand (A : List (L × Formula V L P)) (φ : Formula V L P) : Formula V L P :=
  A.foldl (fun ψ _ => ψ.substLabels (assignment A)) φ

/-- Expand a formula by its own label definitions. -/
def Formula.expandSelf (φ : Formula V L P) : Formula V L P := φ.expand φ.defs

end Labels

/-! ### Eliminability -/

section Elim

variable [DecidableEq V]

/-- Existential closure over a list of variables, as syntax. -/
def Formula.closeList (xs : List V) (φ : Formula V L P) : Formula V L P :=
  xs.foldr Expr.exists_ φ

/-- The translation into predicate calculus with set abstraction. It drops brackets and
presuppositions and replaces label definitions by `⊤`; a summation `Σxφ` becomes the set
abstraction over `x` of `φ` with its other local variables existentially closed. -/
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
