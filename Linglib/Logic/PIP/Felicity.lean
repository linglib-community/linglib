module

public import Linglib.Logic.PIP.Semantics

/-!
# Felicity of PIP formulas

This file defines the felicity operator `F` on the terms and formulas of PIP.
A presupposition `φ|ψ` is felicitous iff `φ` and `ψ` are and `ψ` is true; a
conjunction `φ ∧ ψ` iff `φ` is and, whenever `φ` is true, `ψ` is; a quantifier,
abstraction or summation iff its body is for every value of the variables it
binds; the other connectives and relations iff their parts are. Felicity is
independent of truth. The PIP-value of a formula records its truth, its
felicity, its local variables and its label definitions, and two formulas are
intersubstitutable iff they have the same PIP-value in every model under every
assignment.

## Main definitions

* `Expr.Felicitous` — the felicity operator `F`.
* `Value`, `Formula.value` — the PIP-value of a formula.

## Main statements

* `Formula.felicitous_atom`, `Formula.felicitous_conj`, … — the clauses of
  felicity, as simp lemmas; `Formula.felicitous_disj`, …,
  `Formula.felicitous_some` — the derived connectives.
* `Expr.felicitous_of_presupFree` — every infelicity traces to a
  presupposition.
* `Term.felicitous_sigma_conj_of_felicitous` — felicity of a discourse
  extended by a sentence reduces to the earlier discourse strictly implying
  the new sentence's felicity.

## References

* [keshet-abney-2024]
* [abney-keshet-2025]
* [karttunen-1974]
-/

@[expose] public section

namespace PIP

universe u v w

variable {V : Type u} {L : Type v} {P : ℕ → Type w} {α : Type*}

section Felicity

variable [DecidableEq V]

/-- Felicity: `e|ψ` needs `e` and `ψ` felicitous and `ψ` true; abstraction,
summation and quantification need their bodies felicitous for every value; a
conjunction needs its first conjunct felicitous and, if it is true, its second
— the first conjunct may satisfy the presuppositions of the second. -/
def Expr.Felicitous (M : Model P α) (g : V → Set α) : ∀ {k : Kind}, Expr V L P k → Prop
  | _, .var _ => True
  | _, .bvar _ => True
  | _, .abs x φ => ∀ g', Set.EqOn g' g {x}ᶜ → φ.Felicitous M g'
  | _, .sigma x φ => ∀ g', Set.EqOn g' g {y | y ∉ φ.locals ∧ y ≠ x} → φ.Felicitous M g'
  | _, .inter s t => s.Felicitous M g ∧ t.Felicitous M g
  | _, .empty => True
  | _, .top => True
  | _, .atom _ w ts => w.Felicitous M g ∧ ∀ i, (ts i).Felicitous M g
  | _, .eq s t => s.Felicitous M g ∧ t.Felicitous M g
  | _, .subset s t => s.Felicitous M g ∧ t.Felicitous M g
  | _, .mem s t => s.Felicitous M g ∧ t.Felicitous M g
  | _, .sg t => t.Felicitous M g
  | _, .pl t => t.Felicitous M g
  | _, .neg φ => φ.Felicitous M g
  | _, .conj φ ψ => φ.Felicitous M g ∧ (Formula.Realize M g φ → ψ.Felicitous M g)
  | _, .exists_ x φ => ∀ g', Set.EqOn g' g {x}ᶜ → φ.Felicitous M g'
  | _, .labelDef _ _ => True
  | _, .label _ => False
  | _, .presup e ψ => e.Felicitous M g ∧ ψ.Felicitous M g ∧ Formula.Realize M g ψ

variable (M : Model P α) (g : V → Set α)

@[simp] theorem Term.felicitous_var (x : V) : Expr.Felicitous M g (.var x : Term V L P) :=
  trivial

@[simp] theorem Term.felicitous_bvar (x : V) : Expr.Felicitous M g (.bvar x : Term V L P) :=
  trivial

@[simp] theorem Term.felicitous_empty : Expr.Felicitous M g (.empty : Term V L P) := trivial

@[simp] theorem Term.felicitous_inter (s t : Term V L P) :
    Expr.Felicitous M g (.inter s t) ↔ s.Felicitous M g ∧ t.Felicitous M g := Iff.rfl

@[simp] theorem Expr.felicitous_presup {k : Kind} (e : Expr V L P k) (ψ : Formula V L P) :
    Expr.Felicitous M g (.presup e ψ) ↔
      e.Felicitous M g ∧ ψ.Felicitous M g ∧ Formula.Realize M g ψ := Iff.rfl

theorem Term.felicitous_abs (x : V) (φ : Formula V L P) :
    Expr.Felicitous M g (.abs x φ) ↔ ∀ g', Set.EqOn g' g {x}ᶜ → φ.Felicitous M g' := Iff.rfl

theorem Term.felicitous_sigma (x : V) (φ : Formula V L P) :
    Expr.Felicitous M g (.sigma x φ) ↔
      ∀ g', Set.EqOn g' g {y | y ∉ φ.locals ∧ y ≠ x} → φ.Felicitous M g' := Iff.rfl

theorem Term.felicitous_abs_of_forall {x : V} {φ : Formula V L P}
    (h : ∀ g, φ.Felicitous M g) : Expr.Felicitous M g (.abs x φ) := fun _ _ => h _

theorem Term.felicitous_sigma_of_forall {x : V} {φ : Formula V L P}
    (h : ∀ g, φ.Felicitous M g) : Expr.Felicitous M g (.sigma x φ) := fun _ _ => h _

theorem Term.felicitous_sgPronoun (x : V) (φ : Formula V L P) :
    Expr.Felicitous M g (Term.sgPronoun x φ) ↔
      Expr.Felicitous M g (.sigma x φ) ∧ ∃ a, Term.realize M g (.sigma x φ) = {a} := by
  show Expr.Felicitous M g (.sigma x φ) ∧ Expr.Felicitous M g (.sigma x φ) ∧
    (∃ a, Term.realize M g (.sigma x φ) = {a}) ↔ _
  exact ⟨fun ⟨a, _, c⟩ => ⟨a, c⟩, fun ⟨a, c⟩ => ⟨a, a, c⟩⟩

@[simp] theorem Formula.felicitous_top : Expr.Felicitous M g (.top : Formula V L P) := trivial

@[simp] theorem Formula.felicitous_atom {n : ℕ} (r : P n) (w : Term V L P)
    (ts : Fin n → Term V L P) :
    Expr.Felicitous M g (.atom r w ts) ↔ w.Felicitous M g ∧ ∀ i, (ts i).Felicitous M g :=
  Iff.rfl

@[simp] theorem Formula.felicitous_eq (s t : Term V L P) :
    Expr.Felicitous M g (.eq s t) ↔ s.Felicitous M g ∧ t.Felicitous M g := Iff.rfl

@[simp] theorem Formula.felicitous_subset (s t : Term V L P) :
    Expr.Felicitous M g (.subset s t) ↔ s.Felicitous M g ∧ t.Felicitous M g := Iff.rfl

@[simp] theorem Formula.felicitous_mem (s t : Term V L P) :
    Expr.Felicitous M g (.mem s t) ↔ s.Felicitous M g ∧ t.Felicitous M g := Iff.rfl

@[simp] theorem Formula.felicitous_sg (t : Term V L P) :
    Expr.Felicitous M g (.sg t) ↔ t.Felicitous M g := Iff.rfl

@[simp] theorem Formula.felicitous_pl (t : Term V L P) :
    Expr.Felicitous M g (.pl t) ↔ t.Felicitous M g := Iff.rfl

@[simp] theorem Formula.felicitous_neg (φ : Formula V L P) :
    Expr.Felicitous M g (.neg φ) ↔ φ.Felicitous M g := Iff.rfl

@[simp] theorem Formula.felicitous_conj (φ ψ : Formula V L P) :
    Expr.Felicitous M g (.conj φ ψ) ↔
      φ.Felicitous M g ∧ (Formula.Realize M g φ → ψ.Felicitous M g) := Iff.rfl

theorem Formula.felicitous_exists (x : V) (φ : Formula V L P) :
    Expr.Felicitous M g (.exists_ x φ) ↔
      ∀ g', Set.EqOn g' g {x}ᶜ → φ.Felicitous M g' := Iff.rfl

@[simp] theorem Formula.felicitous_labelDef (X : L) (φ : Formula V L P) :
    Expr.Felicitous M g (.labelDef X φ) := trivial

@[simp] theorem Formula.felicitous_label (X : L) :
    Expr.Felicitous M g (.label X : Formula V L P) ↔ False := Iff.rfl

theorem Expr.felicitous_of_presupFree :
    ∀ {k : Kind} (e : Expr V L P k), e.PresupFree → ∀ g, e.Felicitous M g
  | _, .var _, _, _ => trivial
  | _, .bvar _, _, _ => trivial
  | _, .abs _ φ, h, _ => fun g' _ => Expr.felicitous_of_presupFree φ h g'
  | _, .sigma _ φ, h, _ => fun g' _ => Expr.felicitous_of_presupFree φ h g'
  | _, .inter s t, h, g =>
      ⟨Expr.felicitous_of_presupFree s h.1 g, Expr.felicitous_of_presupFree t h.2 g⟩
  | _, .empty, _, _ => trivial
  | _, .top, _, _ => trivial
  | _, .atom _ w ts, h, g =>
      ⟨Expr.felicitous_of_presupFree w h.1 g,
        fun i => Expr.felicitous_of_presupFree (ts i) (h.2 i (List.mem_finRange i)) g⟩
  | _, .eq s t, h, g =>
      ⟨Expr.felicitous_of_presupFree s h.1 g, Expr.felicitous_of_presupFree t h.2 g⟩
  | _, .subset s t, h, g =>
      ⟨Expr.felicitous_of_presupFree s h.1 g, Expr.felicitous_of_presupFree t h.2 g⟩
  | _, .mem s t, h, g =>
      ⟨Expr.felicitous_of_presupFree s h.1 g, Expr.felicitous_of_presupFree t h.2 g⟩
  | _, .sg t, h, g => Expr.felicitous_of_presupFree t h g
  | _, .pl t, h, g => Expr.felicitous_of_presupFree t h g
  | _, .neg φ, h, g => Expr.felicitous_of_presupFree φ h g
  | _, .conj φ ψ, h, g =>
      ⟨Expr.felicitous_of_presupFree φ h.1 g, fun _ => Expr.felicitous_of_presupFree ψ h.2 g⟩
  | _, .exists_ _ φ, h, _ => fun g' _ => Expr.felicitous_of_presupFree φ h g'
  | _, .labelDef _ _, _, _ => trivial
  | _, .label _, h, _ => h.elim
  | _, .presup _ _, h, _ => h.elim

/-! ### Derived clauses -/

theorem Formula.felicitous_disj (φ ψ : Formula V L P) :
    Expr.Felicitous M g (φ.disj ψ) ↔
      φ.Felicitous M g ∧ (¬ Formula.Realize M g φ → ψ.Felicitous M g) := Iff.rfl

theorem Formula.felicitous_impl (φ ψ : Formula V L P) :
    Expr.Felicitous M g (φ.impl ψ) ↔
      φ.Felicitous M g ∧ (Formula.Realize M g φ → ψ.Felicitous M g) := Iff.rfl

theorem Formula.felicitous_iff (φ ψ : Formula V L P) :
    Expr.Felicitous M g (φ.iff_ ψ) ↔ φ.Felicitous M g ∧ ψ.Felicitous M g := by
  show Expr.Felicitous M g (φ.impl ψ) ∧
    (Formula.Realize M g (φ.impl ψ) → Expr.Felicitous M g (ψ.impl φ)) ↔ _
  rw [Formula.felicitous_impl, Formula.felicitous_impl, Formula.realize_impl]
  constructor
  · rintro ⟨⟨hφ, h₁⟩, h₂⟩
    refine ⟨hφ, ?_⟩
    by_cases hp : Formula.Realize M g φ
    · exact h₁ hp
    · exact (h₂ fun h => absurd h hp).1
  · rintro ⟨hφ, hψ⟩
    exact ⟨⟨hφ, fun _ => hψ⟩, fun _ => ⟨hψ, fun _ => hφ⟩⟩

theorem Formula.felicitous_forall (x : V) (φ : Formula V L P) :
    Expr.Felicitous M g (Formula.forall_ x φ) ↔
      ∀ g', Set.EqOn g' g {x}ᶜ → φ.Felicitous M g' := Iff.rfl

theorem Formula.felicitous_some (s t : Term V L P) :
    Expr.Felicitous M g (Formula.some_ s t) ↔ s.Felicitous M g ∧ t.Felicitous M g :=
  show (s.Felicitous M g ∧ t.Felicitous M g) ∧ True ↔ _ from (and_true _).to_iff

theorem Term.felicitous_sigma_conj (w : V) (γ φ : Formula V L P) :
    Expr.Felicitous M g (.sigma w (.conj γ φ)) ↔
      ∀ g', Set.EqOn g' g {y | y ∉ (Expr.conj γ φ).locals ∧ y ≠ w} →
        γ.Felicitous M g' ∧ (Formula.Realize M g' γ → φ.Felicitous M g') := Iff.rfl

theorem Term.felicitous_sigma_conj_of_felicitous (w : V) (γ φ : Formula V L P)
    (hγ : ∀ g', Set.EqOn g' g {y | y ∉ (Expr.conj γ φ).locals ∧ y ≠ w} → γ.Felicitous M g') :
    Expr.Felicitous M g (.sigma w (.conj γ φ)) ↔
      ∀ g', Set.EqOn g' g {y | y ∉ (Expr.conj γ φ).locals ∧ y ≠ w} →
        (Formula.Realize M g' γ → φ.Felicitous M g') :=
  forall_congr' fun g' => imp_congr_right fun hg => and_iff_right (hγ g' hg)

/-! ### Meanings -/

/-- The PIP-value of a formula: its truth, its felicity, its local variables and
its label definitions. -/
@[ext]
structure Value (V : Type u) (L : Type v) (P : ℕ → Type w) where
  /-- Truth. -/
  truth : Prop
  /-- Felicity. -/
  felicity : Prop
  /-- The free local variables. -/
  locals : List V
  /-- The label definitions. -/
  defs : List (L × Formula V L P)

/-- The PIP-value of a formula. Two formulas are intersubstitutable iff they
have the same value in every model under every assignment; truth-equivalent
formulas need not be. -/
def Formula.value (φ : Formula V L P) : Value V L P :=
  ⟨Formula.Realize M g φ, φ.Felicitous M g, φ.locals, φ.defs⟩

end Felicity

end PIP
