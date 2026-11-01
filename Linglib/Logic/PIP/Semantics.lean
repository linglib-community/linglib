module

public import Mathlib.Data.Set.Lattice.Bounded
public import Linglib.Core.Data.Set.Function
public import Linglib.Logic.PIP.Syntax

/-!
# Semantics of PIP

This file defines the value of a term and the truth of a formula of PIP in a
model, relative to an assignment of pluralities to variables. Pluralities are
sets of atoms. A variable denotes its assignment; set abstraction `⋃{x : φ}` and
summation `Σxφ` denote the union of the values of `x` over the assignments that
agree with the current one outside the bound variables (for summation, also
outside the local variables of `φ`) and satisfy `φ`. Presuppositions and label
definitions do not affect truth, and an unexpanded label is false. A discourse
`φ₁, …, φₙ` means `Σw(φ₁ ∧ … ∧ φₙ)` and is true iff that plurality of worlds is
nonempty.

Both kinds of expression are realized by one recursion, `Expr.Realize`, as a
relation to a point: an atom for a term, nothing for a formula.

## Main definitions

* `Model` — the interpretation of relation symbols over pluralities.
* `LogicalRel.Holds` — the fixed meaning of the logical relations.
* `Expr.Realize`, `Term.realize`, `Formula.Realize` — value and truth relative
  to a model and an assignment.

## Main statements

* `Formula.realize_atom`, `Formula.realize_conj`, … — the clauses of truth,
  as simp lemmas; `Formula.realize_disj`, …, `Formula.realize_some` — the
  derived connectives.
* `Formula.realize_ex_iff_abs_nonempty` — `∃xφ` is true iff `⋃{x : φ}` is
  nonempty, when `φ` is false of the null plurality.
* `Term.realize_sigma_eq`, `Term.realize_sigma_eq_of_mem_locals` — the value of a
  summation from a characterization of its body; `Term.realize_sigma_eq_image`,
  `Term.realize_sigma_eq_of_distributive` — over singular and distributive descriptions.
* `Expr.realize_congr` — values and truth depend only on the variables occurring in an
  expression.
* `Expr.realize_elim` — the PIP constructs are eliminable: the translation
  preserves values and truth.

## References

* [keshet-abney-2024]
* [abney-keshet-2025]
-/

@[expose] public section

namespace PIP

universe u v w

variable {V : Type u} {L : Type v} {P : ℕ → Type w} {α : Type*}

/-- A model: pluralities are sets of atoms `α`, and each `n`-ary relation symbol
is interpreted over a world plurality and a tuple of `n` pluralities. -/
structure Model (P : ℕ → Type w) (α : Type u) where
  /-- The interpretation of relation symbols. -/
  I : ∀ {n : ℕ}, P n → Set α → (Fin n → Set α) → Prop

/-- The point at which an expression of a kind is realized: an atom, whose
membership in a term's value is at stake, or nothing for a formula. -/
def Kind.Point (α : Type u) : Kind → Type u
  | .term => α
  | .formula => PUnit

/-- The meaning of the logical relations on pluralities. Membership `s ∈ t` holds when `s` is the
singleton of an atom of `t`. -/
def LogicalRel.Holds : ∀ {n : ℕ}, LogicalRel n → (Fin n → Set α) → Prop
  | _, .eq, S => S 0 = S 1
  | _, .subset, S => S 0 ⊆ S 1
  | _, .mem, S => ∃ a, S 0 = {a} ∧ a ∈ S 1
  | _, .sg, S => ∃ a, S 0 = {a}
  | _, .pl, S => ∃ a b, a ≠ b ∧ a ∈ S 0 ∧ b ∈ S 0

section Semantics

variable [DecidableEq V]

/-- Realization: membership of an atom in the value of a term, and truth of a
formula. A variable denotes its assignment, abstraction and summation the union
of the values of the bound variable over assignments agreeing outside the bound
variables; a formula is true classically, with presuppositions and label
definitions transparent and an unexpanded label false. -/
def Expr.Realize (M : Model P α) (g : V → Set α) :
    ∀ {k : Kind}, Expr V L P k → Kind.Point α k → Prop
  | _, .var x, a => a ∈ g x
  | _, .bvar x, a => a ∈ g x
  | _, .abs x φ, a => ∃ g', Set.EqOn g' g {x}ᶜ ∧ a ∈ g' x ∧ φ.Realize M g' .unit
  | _, .sigma x φ, a =>
      ∃ g', Set.EqOn g' g {y | y ∉ φ.locals ∧ y ≠ x} ∧ a ∈ g' x ∧ φ.Realize M g' .unit
  | _, .inter s t, a => s.Realize M g a ∧ t.Realize M g a
  | _, .empty, _ => False
  | _, .top, _ => True
  | _, .atom r w ts, _ => M.I r {a | w.Realize M g a} fun i => {a | (ts i).Realize M g a}
  | _, .rel R ts, _ => R.Holds fun i => {a | (ts i).Realize M g a}
  | _, .neg φ, _ => ¬ φ.Realize M g .unit
  | _, .conj φ ψ, _ => φ.Realize M g .unit ∧ ψ.Realize M g .unit
  | _, .ex x φ, _ => ∃ g', Set.EqOn g' g {x}ᶜ ∧ φ.Realize M g' .unit
  | _, .labelDef _ _, _ => True
  | _, .label _, _ => False
  | _, .presup e _, a => e.Realize M g a

variable (M : Model P α) (g : V → Set α)

/-- The value of a term. -/
def Term.realize (t : Term V L P) : Set α := {a | t.Realize M g a}

/-- Truth of a formula. -/
def Formula.Realize (φ : Formula V L P) : Prop := Expr.Realize M g φ .unit

@[simp] theorem Term.mem_realize {t : Term V L P} {a : α} :
    a ∈ Term.realize M g t ↔ t.Realize M g a := Iff.rfl

@[simp] theorem Term.realize_var (x : V) : Term.realize M g (.var x : Term V L P) = g x := rfl

@[simp] theorem Term.realize_bvar (x : V) : Term.realize M g (.bvar x : Term V L P) = g x := rfl

@[simp] theorem Term.realize_inter (s t : Term V L P) :
    Term.realize M g (.inter s t) = Term.realize M g s ∩ Term.realize M g t := rfl

@[simp] theorem Term.realize_empty : Term.realize M g (.empty : Term V L P) = ∅ := rfl

@[simp] theorem Term.realize_presup (t : Term V L P) (ψ : Formula V L P) :
    Term.realize M g (.presup t ψ) = Term.realize M g t := rfl

@[simp] theorem Term.mem_realize_abs (x : V) (φ : Formula V L P) (a : α) :
    a ∈ Term.realize M g (.abs x φ) ↔ ∃ X, a ∈ X ∧ Formula.Realize M (Function.update g x X) φ :=
  Set.exists_eqOn_compl_singleton_iff.trans <| by simp only [Function.update_self]; rfl

theorem Term.mem_realize_sigma (x : V) (φ : Formula V L P) (a : α) :
    a ∈ Term.realize M g (.sigma x φ) ↔
      ∃ g', Set.EqOn g' g {y | y ∉ φ.locals ∧ y ≠ x} ∧ a ∈ g' x ∧ Formula.Realize M g' φ :=
  Iff.rfl

@[simp] theorem Formula.realize_top : Formula.Realize M g (.top : Formula V L P) ↔ True :=
  Iff.rfl

@[simp] theorem Formula.realize_atom {n : ℕ} (r : P n) (w : Term V L P)
    (ts : Fin n → Term V L P) :
    Formula.Realize M g (.atom r w ts) ↔ M.I r (Term.realize M g w) (Term.realize M g ∘ ts) :=
  Iff.rfl

theorem Formula.realize_rel {n : ℕ} (R : LogicalRel n) (ts : Fin n → Term V L P) :
    Formula.Realize M g (.rel R ts) ↔ R.Holds (Term.realize M g ∘ ts) := Iff.rfl

@[simp] theorem Formula.realize_eq (s t : Term V L P) :
    Formula.Realize M g (.eq s t) ↔ Term.realize M g s = Term.realize M g t := Iff.rfl

@[simp] theorem Formula.realize_subset (s t : Term V L P) :
    Formula.Realize M g (.subset s t) ↔ Term.realize M g s ⊆ Term.realize M g t := Iff.rfl

@[simp] theorem Formula.realize_mem (s t : Term V L P) :
    Formula.Realize M g (.mem s t) ↔
      ∃ a, Term.realize M g s = {a} ∧ a ∈ Term.realize M g t := Iff.rfl

@[simp] theorem Formula.realize_sg (t : Term V L P) :
    Formula.Realize M g (.sg t) ↔ ∃ a, Term.realize M g t = {a} := Iff.rfl

@[simp] theorem Formula.realize_pl (t : Term V L P) :
    Formula.Realize M g (.pl t) ↔
      ∃ a b, a ≠ b ∧ a ∈ Term.realize M g t ∧ b ∈ Term.realize M g t := Iff.rfl

@[simp] theorem Formula.realize_neg (φ : Formula V L P) :
    Formula.Realize M g (.neg φ) ↔ ¬ Formula.Realize M g φ := Iff.rfl

@[simp] theorem Formula.realize_conj (φ ψ : Formula V L P) :
    Formula.Realize M g (.conj φ ψ) ↔ Formula.Realize M g φ ∧ Formula.Realize M g ψ := Iff.rfl

@[simp] theorem Formula.realize_ex (x : V) (φ : Formula V L P) :
    Formula.Realize M g (.ex x φ) ↔ ∃ X, Formula.Realize M (Function.update g x X) φ :=
  Set.exists_eqOn_compl_singleton_iff

@[simp] theorem Formula.realize_presup (φ ψ : Formula V L P) :
    Formula.Realize M g (.presup φ ψ) ↔ Formula.Realize M g φ := Iff.rfl

@[simp] theorem Formula.realize_labelDef (X : L) (φ : Formula V L P) :
    Formula.Realize M g (.labelDef X φ) ↔ True := Iff.rfl

@[simp] theorem Formula.realize_label (X : L) :
    Formula.Realize M g (.label X : Formula V L P) ↔ False := Iff.rfl

/-! ### Derived clauses -/

@[simp] theorem Formula.realize_disj (φ ψ : Formula V L P) :
    Formula.Realize M g (φ.disj ψ) ↔ Formula.Realize M g φ ∨ Formula.Realize M g ψ :=
  show ¬(¬Formula.Realize M g φ ∧ ¬Formula.Realize M g ψ) ↔ _ from or_iff_not_and_not.symm

@[simp] theorem Formula.realize_impl (φ ψ : Formula V L P) :
    Formula.Realize M g (φ.impl ψ) ↔ (Formula.Realize M g φ → Formula.Realize M g ψ) :=
  show ¬(Formula.Realize M g φ ∧ ¬Formula.Realize M g ψ) ↔ _ from not_and_not_right

@[simp] theorem Formula.realize_iff (φ ψ : Formula V L P) :
    Formula.Realize M g (φ.iff ψ) ↔ (Formula.Realize M g φ ↔ Formula.Realize M g ψ) := by
  show Formula.Realize M g (φ.impl ψ) ∧ Formula.Realize M g (ψ.impl φ) ↔ _
  rw [Formula.realize_impl, Formula.realize_impl]
  exact iff_iff_implies_and_implies.symm

@[simp] theorem Formula.realize_all (x : V) (φ : Formula V L P) :
    Formula.Realize M g (Formula.all x φ) ↔ ∀ X, Formula.Realize M (Function.update g x X) φ :=
  (Formula.realize_neg _ _ _).trans <| by simp

@[simp] theorem Formula.realize_some (s t : Term V L P) :
    Formula.Realize M g (Formula.some s t) ↔ (Term.realize M g s ∩ Term.realize M g t).Nonempty :=
  show ¬(Term.realize M g s ∩ Term.realize M g t = ∅) ↔ _ from Set.nonempty_iff_ne_empty.symm

/-- `∃xφ` is true iff `⋃{x : φ}` is nonempty, provided `φ` is false when `x` is
the null plurality, the standing assumption that predicates are false of the
null individual. -/
theorem Formula.realize_ex_iff_abs_nonempty (x : V) (φ : Formula V L P)
    (h : ¬ Formula.Realize M (Function.update g x ∅) φ) :
    Formula.Realize M g (.ex x φ) ↔ (Term.realize M g (.abs x φ)).Nonempty := by
  simp only [Formula.realize_ex, Set.Nonempty, Term.mem_realize_abs]
  refine ⟨fun ⟨X, hX⟩ => ?_, fun ⟨_, X, _, hX⟩ => ⟨X, hX⟩⟩
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 fun he => h (he ▸ hX)
  exact ⟨a, X, ha, hX⟩

/-- The value of a summation whose body, on the assignments agreeing outside the
summation variable and its locals, depends on the summation variable's value
alone: the sum of the pluralities satisfying that condition. -/
theorem Term.realize_sigma_eq {x : V} {φ : Formula V L P} {B : Set α → Prop}
    (hφ : ∀ g', Set.EqOn g' g {y | y ∉ φ.locals ∧ y ≠ x} →
      (Formula.Realize M g' φ ↔ B (g' x))) :
    Term.realize M g (.sigma x φ) = ⋃₀ {X | B X} := by
  ext a
  rw [Term.mem_realize_sigma, Set.mem_sUnion]
  constructor
  · rintro ⟨g', hg, ha, hr⟩
    exact ⟨g' x, (hφ g' hg).1 hr, ha⟩
  · rintro ⟨X, hB, ha⟩
    have hg : Set.EqOn (Function.update g x X) g {y | y ∉ φ.locals ∧ y ≠ x} :=
      fun y hy => Function.update_of_ne hy.2 _ _
    exact ⟨_, hg, by simpa, (hφ _ hg).2 (by simpa)⟩

/-- The value of a summation whose body depends on the summation variable's value and on
that of a local variable `y`: the sum of the pluralities related to some plurality, the
local being summed away. -/
theorem Term.realize_sigma_eq_of_mem_locals {x y : V} (hxy : y ≠ x) {φ : Formula V L P}
    {C : Set α → Set α → Prop}
    (hφ : ∀ g', Set.EqOn g' g {z | z ∉ φ.locals ∧ z ≠ x} →
      (Formula.Realize M g' φ ↔ C (g' x) (g' y)))
    (hy : y ∈ φ.locals) :
    Term.realize M g (.sigma x φ) = ⋃₀ {X | ∃ Y, C X Y} := by
  ext a
  rw [Term.mem_realize_sigma, Set.mem_sUnion]
  constructor
  · rintro ⟨g', hg, ha, hr⟩
    exact ⟨g' x, ⟨g' y, (hφ g' hg).1 hr⟩, ha⟩
  · rintro ⟨X, ⟨Y, hC⟩, ha⟩
    have hg : Set.EqOn (Function.update (Function.update g x X) y Y) g
        {z | z ∉ φ.locals ∧ z ≠ x} := fun z hz => by
      rw [Function.update_of_ne fun h : z = y => hz.1 (h ▸ hy), Function.update_of_ne hz.2]
    refine ⟨_, hg, by simpa [Function.update_of_ne hxy.symm], (hφ _ hg).2 ?_⟩
    rwa [Function.update_self, Function.update_of_ne hxy.symm, Function.update_self]

/-- A summation over a singular description, true of the singletons of the images of `s`:
the plurality of those images. -/
theorem Term.realize_sigma_eq_image {β : Type*} {x : V} {φ : Formula V L P} {f : β → α}
    {s : Set β}
    (hφ : ∀ g', Set.EqOn g' g {y | y ∉ φ.locals ∧ y ≠ x} →
      (Formula.Realize M g' φ ↔ ∃ b, g' x = {f b} ∧ b ∈ s)) :
    Term.realize M g (.sigma x φ) = f '' s := by
  rw [Term.realize_sigma_eq M g (B := fun X => ∃ b, X = {f b} ∧ b ∈ s) hφ]
  ext a
  simp [and_comm, eq_comm]

/-- A summation over a distributive description, true of the nonempty pluralities within
`s`: `s` itself. -/
theorem Term.realize_sigma_eq_of_distributive {x : V} {φ : Formula V L P} {s : Set α}
    (hφ : ∀ g', Set.EqOn g' g {y | y ∉ φ.locals ∧ y ≠ x} →
      (Formula.Realize M g' φ ↔ (g' x).Nonempty ∧ g' x ⊆ s)) :
    Term.realize M g (.sigma x φ) = s := by
  rw [Term.realize_sigma_eq M g (B := fun X => X.Nonempty ∧ X ⊆ s) hφ]
  ext a
  simp only [Set.mem_sUnion, Set.mem_ofPred_eq]
  exact ⟨fun ⟨_, ⟨_, hX⟩, ha⟩ => hX ha, fun ha => ⟨{a}, ⟨⟨a, rfl⟩, by simpa⟩, rfl⟩⟩

/-! ### Dependence on the variables -/

/-- Values and truth depend only on the variables occurring in an expression. -/
theorem Expr.realize_congr :
    ∀ {k : Kind} (e : Expr V L P k) {g g' : V → Set α}, Set.EqOn g g' e.vars →
      ∀ a : Kind.Point α k, (e.Realize M g a ↔ e.Realize M g' a)
  | _, .var x, _, _, h, a => by rw [Expr.Realize, Expr.Realize, h (Set.mem_singleton x)]
  | _, .bvar x, _, _, h, a => by rw [Expr.Realize, Expr.Realize, h (Set.mem_singleton x)]
  | _, .abs x φ, _, _, h, a =>
      Set.exists_eqOn_congr (s := insert x φ.vars) (h.mono Set.inter_subset_left)
        fun _ _ h' => and_congr (by rw [h' (Set.mem_insert x _)])
          (Expr.realize_congr φ (h'.mono (Set.subset_insert _ _)) .unit)
  | _, .sigma x φ, _, _, h, a =>
      Set.exists_eqOn_congr (s := insert x φ.vars) (h.mono Set.inter_subset_left)
        fun _ _ h' => and_congr (by rw [h' (Set.mem_insert x _)])
          (Expr.realize_congr φ (h'.mono (Set.subset_insert _ _)) .unit)
  | _, .inter s t, _, _, h, a =>
      and_congr (Expr.realize_congr s (h.mono Set.subset_union_left) a)
        (Expr.realize_congr t (h.mono Set.subset_union_right) a)
  | _, .empty, _, _, _, _ => Iff.rfl
  | _, .top, _, _, _, _ => Iff.rfl
  | _, .atom r w ts, _, _, h, _ =>
      iff_of_eq (congrArg₂ (M.I r)
        (Set.ext fun a => Expr.realize_congr w (h.mono Set.subset_union_left) a)
        (funext fun i => Set.ext fun a => Expr.realize_congr (ts i)
          (h.mono (Set.subset_union_of_subset_right (Set.subset_iUnion (fun i => (ts i).vars) i)
            _)) a))
  | _, .rel R ts, _, _, h, _ =>
      iff_of_eq (congrArg R.Holds (funext fun i => Set.ext fun a => Expr.realize_congr (ts i)
        (h.mono (Set.subset_iUnion (fun i => (ts i).vars) i)) a))
  | _, .neg φ, _, _, h, _ => not_congr (Expr.realize_congr φ h .unit)
  | _, .conj φ ψ, _, _, h, _ =>
      and_congr (Expr.realize_congr φ (h.mono Set.subset_union_left) .unit)
        (Expr.realize_congr ψ (h.mono Set.subset_union_right) .unit)
  | _, .ex x φ, _, _, h, _ =>
      Set.exists_eqOn_congr (s := insert x φ.vars) (h.mono Set.inter_subset_left)
        fun _ _ h' => Expr.realize_congr φ (h'.mono (Set.subset_insert _ _)) .unit
  | _, .labelDef _ _, _, _, _, _ => Iff.rfl
  | _, .label _, _, _, _, _ => Iff.rfl
  | _, .presup e _, _, _, h, a => Expr.realize_congr e (h.mono Set.subset_union_left) a

theorem Formula.realize_congr {φ : Formula V L P} {g g' : V → Set α} (h : Set.EqOn g g' φ.vars) :
    Formula.Realize M g φ ↔ Formula.Realize M g' φ :=
  Expr.realize_congr M φ h .unit

/-! ### Eliminability -/

theorem Formula.realize_closeList (xs : List V) (φ : Formula V L P) :
    ∀ g : V → Set α, Formula.Realize M g (φ.closeList xs) ↔
      ∃ g', Set.EqOn g' g {y | y ∉ xs} ∧ Formula.Realize M g' φ := by
  induction xs with
  | nil =>
    refine fun g => ⟨fun h => ⟨g, fun _ _ => rfl, h⟩, ?_⟩
    rintro ⟨g', hg, h⟩
    rwa [show g' = g from funext fun y => hg (by simp)] at h
  | cons x xs ih =>
    intro g
    show (∃ g₁, Set.EqOn g₁ g {x}ᶜ ∧ Formula.Realize M g₁ (φ.closeList xs)) ↔ _
    simp only [ih]
    constructor
    · rintro ⟨g₁, hg₁, g', hg', h⟩
      refine ⟨g', fun y hy => ?_, h⟩
      simp only [List.mem_cons, not_or, Set.mem_ofPred_eq] at hy
      exact (hg' hy.2).trans (hg₁ hy.1)
    · rintro ⟨g', hg', h⟩
      refine ⟨Function.update g x (g' x), fun y hy => Function.update_of_ne hy _ _, g', ?_, h⟩
      intro y hy
      by_cases hyx : y = x
      · subst hyx; simp
      · rw [Function.update_of_ne hyx]
        exact hg' (by simp only [Set.mem_ofPred_eq, List.mem_cons, not_or]; exact ⟨hyx, hy⟩)

/-- The PIP constructs are eliminable: the translation preserves values and
truth. -/
theorem Expr.realize_elim :
    ∀ {k : Kind} (e : Expr V L P k) (g : V → Set α) (a : Kind.Point α k),
      e.elim.Realize M g a ↔ e.Realize M g a
  | _, .var _, _, _ => Iff.rfl
  | _, .bvar _, _, _ => Iff.rfl
  | _, .abs x φ, g, a =>
      show (∃ g', Set.EqOn g' g {x}ᶜ ∧ a ∈ g' x ∧ φ.elim.Realize M g' .unit) ↔ ∃ g', _ from
        exists_congr fun _ => and_congr_right fun _ => and_congr_right fun _ =>
          Expr.realize_elim φ _ .unit
  | _, .sigma x φ, g, a => by
      show (∃ g₁, Set.EqOn g₁ g {x}ᶜ ∧ a ∈ g₁ x ∧
          Formula.Realize M g₁ (Formula.closeList _ φ.elim)) ↔
        ∃ g', Set.EqOn g' g {y | y ∉ φ.locals ∧ y ≠ x} ∧ a ∈ g' x ∧ Formula.Realize M g' φ
      simp only [Formula.realize_closeList]
      simp only [Formula.Realize, Expr.realize_elim φ]
      constructor
      · rintro ⟨g₁, hg₁, ha, g', hg', h⟩
        refine ⟨g', fun y hy => ?_, ?_, h⟩
        · have hy' : y ∉ φ.locals.filter (· ≠ x) := fun h' => hy.1 (List.mem_filter.1 h').1
          exact (hg' hy').trans (hg₁ hy.2)
        · rwa [hg' (by simp)]
      · rintro ⟨g', hg', ha, h⟩
        refine ⟨Function.update g x (g' x), fun y hy => Function.update_of_ne hy _ _,
          by simpa using ha, g', fun y hy => ?_, h⟩
        by_cases hyx : y = x
        · subst hyx; simp
        · rw [Function.update_of_ne hyx]
          exact hg' ⟨fun hl => hy (List.mem_filter.2 ⟨hl, by simpa using hyx⟩), hyx⟩
  | _, .inter s t, g, a => and_congr (Expr.realize_elim s g a) (Expr.realize_elim t g a)
  | _, .empty, _, _ => Iff.rfl
  | _, .top, _, _ => Iff.rfl
  | _, .atom r w ts, g, _ =>
      iff_of_eq (congrArg₂ (M.I r) (Set.ext fun a => Expr.realize_elim w g a)
        (funext fun i => Set.ext fun a => by
          rw [Set.mem_ofPred_eq, FinVec.etaExpand_eq]; exact Expr.realize_elim (ts i) g a))
  | _, .rel R ts, g, _ =>
      iff_of_eq (congrArg R.Holds (funext fun i => Set.ext fun a => by
        rw [Set.mem_ofPred_eq, FinVec.etaExpand_eq]; exact Expr.realize_elim (ts i) g a))
  | _, .neg φ, g, _ => not_congr (Expr.realize_elim φ g .unit)
  | _, .conj φ ψ, g, _ => and_congr (Expr.realize_elim φ g .unit) (Expr.realize_elim ψ g .unit)
  | _, .ex _ φ, _, _ =>
      exists_congr fun _ => and_congr_right fun _ => Expr.realize_elim φ _ .unit
  | _, .labelDef _ _, _, _ => Iff.rfl
  | _, .label _, _, _ => Iff.rfl
  | _, .presup e _, g, a => Expr.realize_elim e g a

theorem Term.realize_elim (t : Term V L P) : Term.realize M g t.elim = Term.realize M g t :=
  Set.ext fun a => Expr.realize_elim M t g a

theorem Formula.realize_elim (φ : Formula V L P) :
    Formula.Realize M g φ.elim ↔ Formula.Realize M g φ :=
  Expr.realize_elim M φ g .unit

end Semantics

end PIP
