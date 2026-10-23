module

public import Linglib.Logic.PIP.Semantics
public import Linglib.Logic.Trivalent.Pointwise

/-!
# Felicity of PIP formulas

This file defines the felicity operator `F` on the terms and formulas of PIP. Felicity is
independent of truth, and the truth of a first conjunct may satisfy the presuppositions of the
second. Read as one trivalent value, undefined where a formula is infelicitous, truth and felicity
compose by Peters' Middle Kleene connectives and the Weak Kleene quantifiers. Two formulas are
intersubstitutable when they agree in truth and felicity in every model and have the same local
variables and label definitions.

## Main definitions

* `PIP.Expr.Felicitous`: the felicity operator `F`.
* `PIP.Formula.toTrivalent`: truth and felicity as one trivalent value.
* `PIP.Formula.Intersubstitutable`: sameness of meaning.

## Main statements

* `PIP.Expr.felicitous_of_presupFree`: every infelicity traces to a presupposition.
* `PIP.Expr.felicitous_congr`: felicity depends only on the variables occurring in an
  expression.
* `PIP.Formula.toTrivalent_conj`, `PIP.Formula.toTrivalent_exists`: conjunction is Middle Kleene
  and existential quantification Weak Kleene.

## Implementation notes

`Expr.Felicitous` is the presuppositional condition on the felicity of a discourse. PIP also
requires a discourse to have no free variables and consistent definitions for the labels it uses,
which are not modelled here. A label is interpreted by expanding it (`Formula.expand`) before
evaluation, and a label left unexpanded is false and infelicitous. A meaning in PIP takes a label
assignment as an argument, which plays no role on formulas without label uses, so
intersubstitutability quantifies over models and assignments only.

## References

* [keshet-abney-2024]
* [abney-keshet-2025]
* [karttunen-1974-presupposition]
* [peters-1979]
* [blamey-1986]
-/

@[expose] public section

namespace PIP

universe u v w

variable {V : Type u} {L : Type v} {P : ℕ → Type w} {α : Type*}

section Felicity

variable [DecidableEq V]

/-- The felicity operator ((33)–(37) and (39d)–(39f) of [abney-keshet-2025]): `e|ψ` needs `e`
and `ψ` felicitous and `ψ` true, and a conjunction its first conjunct felicitous and, where that
conjunct is true, its second; abstraction, summation and quantification need their bodies
felicitous for every value of the variables they bind, and the other constructions their
parts. -/
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

@[simp] theorem Term.felicitous_abs (x : V) (φ : Formula V L P) :
    Expr.Felicitous M g (.abs x φ) ↔ ∀ X, φ.Felicitous M (Function.update g x X) :=
  Set.forall_eqOn_compl_singleton_iff

theorem Term.felicitous_sigma (x : V) (φ : Formula V L P) :
    Expr.Felicitous M g (.sigma x φ) ↔
      ∀ g', Set.EqOn g' g {y | y ∉ φ.locals ∧ y ≠ x} → φ.Felicitous M g' := Iff.rfl

theorem Term.felicitous_sigma_of_forall {x : V} {φ : Formula V L P}
    (h : ∀ g, φ.Felicitous M g) : Expr.Felicitous M g (.sigma x φ) := fun _ _ => h _

@[simp] theorem Term.felicitous_sgPronoun (x : V) (φ : Formula V L P) :
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

@[simp] theorem Formula.felicitous_exists (x : V) (φ : Formula V L P) :
    Expr.Felicitous M g (.exists_ x φ) ↔ ∀ X, φ.Felicitous M (Function.update g x X) :=
  Set.forall_eqOn_compl_singleton_iff

@[simp] theorem Formula.felicitous_labelDef (X : L) (φ : Formula V L P) :
    Expr.Felicitous M g (.labelDef X φ) := trivial

@[simp] theorem Formula.felicitous_label (X : L) :
    Expr.Felicitous M g (.label X : Formula V L P) ↔ False := Iff.rfl

/-- Every infelicity traces to a presupposition: an expression without
presuppositions is felicitous. -/
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

/-- Felicity depends only on the variables occurring in an expression. -/
theorem Expr.felicitous_congr :
    ∀ {k : Kind} (e : Expr V L P k) {g g' : V → Set α}, Set.EqOn g g' e.vars →
      (e.Felicitous M g ↔ e.Felicitous M g')
  | _, .var _, _, _, _ => Iff.rfl
  | _, .bvar _, _, _, _ => Iff.rfl
  | _, .abs x φ, _, _, h =>
      Set.forall_eqOn_congr (s := insert x φ.vars) (h.mono Set.inter_subset_left)
        fun _ _ h' => Expr.felicitous_congr φ (h'.mono (Set.subset_insert _ _))
  | _, .sigma x φ, _, _, h =>
      Set.forall_eqOn_congr (s := insert x φ.vars) (h.mono Set.inter_subset_left)
        fun _ _ h' => Expr.felicitous_congr φ (h'.mono (Set.subset_insert _ _))
  | _, .inter s t, _, _, h =>
      and_congr (Expr.felicitous_congr s (h.mono Set.subset_union_left))
        (Expr.felicitous_congr t (h.mono Set.subset_union_right))
  | _, .empty, _, _, _ => Iff.rfl
  | _, .top, _, _, _ => Iff.rfl
  | _, .atom _ w ts, _, _, h =>
      and_congr (Expr.felicitous_congr w (h.mono Set.subset_union_left))
        (forall_congr' fun i => Expr.felicitous_congr (ts i)
          (h.mono (Set.subset_union_of_subset_right (Set.subset_iUnion (fun i => (ts i).vars) i)
            _)))
  | _, .eq s t, _, _, h =>
      and_congr (Expr.felicitous_congr s (h.mono Set.subset_union_left))
        (Expr.felicitous_congr t (h.mono Set.subset_union_right))
  | _, .subset s t, _, _, h =>
      and_congr (Expr.felicitous_congr s (h.mono Set.subset_union_left))
        (Expr.felicitous_congr t (h.mono Set.subset_union_right))
  | _, .mem s t, _, _, h =>
      and_congr (Expr.felicitous_congr s (h.mono Set.subset_union_left))
        (Expr.felicitous_congr t (h.mono Set.subset_union_right))
  | _, .sg t, _, _, h => Expr.felicitous_congr t h
  | _, .pl t, _, _, h => Expr.felicitous_congr t h
  | _, .neg φ, _, _, h => Expr.felicitous_congr φ h
  | _, .conj φ ψ, _, _, h =>
      and_congr (Expr.felicitous_congr φ (h.mono Set.subset_union_left))
        (imp_congr (Formula.realize_congr M (h.mono Set.subset_union_left))
          (Expr.felicitous_congr ψ (h.mono Set.subset_union_right)))
  | _, .exists_ x φ, _, _, h =>
      Set.forall_eqOn_congr (s := insert x φ.vars) (h.mono Set.inter_subset_left)
        fun _ _ h' => Expr.felicitous_congr φ (h'.mono (Set.subset_insert _ _))
  | _, .labelDef _ _, _, _, _ => Iff.rfl
  | _, .label _, _, _, _ => Iff.rfl
  | _, .presup e ψ, _, _, h =>
      and_congr (Expr.felicitous_congr e (h.mono Set.subset_union_left))
        (and_congr (Expr.felicitous_congr ψ (h.mono Set.subset_union_right))
          (Formula.realize_congr M (h.mono Set.subset_union_right)))

/-- With a presupposition-free presupposition, `e|ψ` is felicitous iff `e` is and `ψ` is true,
the clause (41) of [keshet-abney-2024]. -/
theorem Expr.felicitous_presup_of_presupFree {k : Kind} (e : Expr V L P k) {ψ : Formula V L P}
    (hψ : ψ.PresupFree) :
    Expr.Felicitous M g (.presup e ψ) ↔ e.Felicitous M g ∧ Formula.Realize M g ψ :=
  and_congr_right' <| and_iff_right <| ψ.felicitous_of_presupFree M hψ g

/-! ### Derived clauses -/

@[simp] theorem Formula.felicitous_disj (φ ψ : Formula V L P) :
    Expr.Felicitous M g (φ.disj ψ) ↔
      φ.Felicitous M g ∧ (¬ Formula.Realize M g φ → ψ.Felicitous M g) := Iff.rfl

@[simp] theorem Formula.felicitous_impl (φ ψ : Formula V L P) :
    Expr.Felicitous M g (φ.impl ψ) ↔
      φ.Felicitous M g ∧ (Formula.Realize M g φ → ψ.Felicitous M g) := Iff.rfl

@[simp] theorem Formula.felicitous_iff (φ ψ : Formula V L P) :
    Expr.Felicitous M g (φ.iff_ ψ) ↔ φ.Felicitous M g ∧ ψ.Felicitous M g := by
  show Expr.Felicitous M g ((φ.impl ψ).conj (ψ.impl φ)) ↔ _
  simp only [felicitous_conj, felicitous_impl, realize_impl]
  tauto

@[simp] theorem Formula.felicitous_forall (x : V) (φ : Formula V L P) :
    Expr.Felicitous M g (Formula.forall_ x φ) ↔ ∀ X, φ.Felicitous M (Function.update g x X) :=
  Formula.felicitous_exists M g x (.neg φ)

@[simp] theorem Formula.felicitous_some (s t : Term V L P) :
    Expr.Felicitous M g (Formula.some_ s t) ↔ s.Felicitous M g ∧ t.Felicitous M g :=
  show (s.Felicitous M g ∧ t.Felicitous M g) ∧ True ↔ _ from (and_true _).to_iff

/-! ### Truth and felicity as one trivalent value -/

open Classical in
/-- The trivalent value of a formula: undefined where it is infelicitous, and its truth value
elsewhere. -/
noncomputable def Formula.toTrivalent (φ : Formula V L P) : SignType :=
  if φ.Felicitous M g then SignType.ofProp (Formula.Realize M g φ) else 0

variable {M g} {φ ψ : Formula V L P}

@[simp] theorem Formula.toTrivalent_eq_zero_iff : φ.toTrivalent M g = 0 ↔ ¬ φ.Felicitous M g := by
  unfold toTrivalent; split_ifs <;> simp_all

@[simp] theorem Formula.toTrivalent_eq_one_iff :
    φ.toTrivalent M g = 1 ↔ φ.Felicitous M g ∧ Formula.Realize M g φ := by
  unfold toTrivalent; split_ifs <;> simp_all

@[simp] theorem Formula.toTrivalent_eq_neg_one_iff :
    φ.toTrivalent M g = -1 ↔ φ.Felicitous M g ∧ ¬ Formula.Realize M g φ := by
  unfold toTrivalent; split_ifs <;> simp_all

variable (M g)

@[simp] theorem Formula.toTrivalent_top : Formula.toTrivalent M g (.top : Formula V L P) = 1 := by
  simp

theorem Formula.toTrivalent_neg : Formula.toTrivalent M g (.neg φ) = -φ.toTrivalent M g :=
  SignType.eq_of_eq_zero_iff_of_eq_one_iff (by simp) (by simp)

/-- Conjunction is Peters' Middle Kleene conjunction ([keshet-abney-2024], fn. 21). -/
theorem Formula.toTrivalent_conj :
    Formula.toTrivalent M g (.conj φ ψ) = (φ.toTrivalent M g).meetMiddle (ψ.toTrivalent M g) :=
  SignType.eq_of_eq_zero_iff_of_eq_one_iff (by simp; tauto) (by simp; tauto)

theorem Formula.toTrivalent_disj :
    (φ.disj ψ).toTrivalent M g = (φ.toTrivalent M g).joinMiddle (ψ.toTrivalent M g) :=
  SignType.eq_of_eq_zero_iff_of_eq_one_iff (by simp; tauto) (by simp; tauto)

theorem Formula.toTrivalent_impl :
    (φ.impl ψ).toTrivalent M g = (-φ.toTrivalent M g).joinMiddle (ψ.toTrivalent M g) :=
  SignType.eq_of_eq_zero_iff_of_eq_one_iff (by simp; tauto) (by simp; tauto)

/-- A presupposition is the transplication of [blamey-1986]: `e|ψ` is undefined unless `ψ` is
true, and otherwise has the value of `e`. -/
theorem Formula.toTrivalent_presup :
    Formula.toTrivalent M g (.presup φ ψ) =
      if ψ.toTrivalent M g = 1 then φ.toTrivalent M g else 0 := by
  split_ifs with h
  · exact SignType.eq_of_eq_zero_iff_of_eq_one_iff (by simp_all) (by simp_all)
  · simp_all

/-- Existential quantification is Weak Kleene: a presupposition projects universally from its
scope. -/
theorem Formula.toTrivalent_exists (x : V) :
    Formula.toTrivalent M g (.exists_ x φ) =
      Trivalent.existsWeak fun X => φ.toTrivalent M (Function.update g x X) :=
  SignType.eq_of_eq_zero_iff_of_eq_one_iff (by simp) <| by
    simp only [toTrivalent_eq_one_iff, felicitous_exists, realize_exists,
      Trivalent.existsWeak_eq_one_iff, ne_eq, toTrivalent_eq_zero_iff, not_not]
    exact ⟨fun ⟨hF, X, hX⟩ => ⟨hF, X, hF X, hX⟩, fun ⟨hF, X, _, hX⟩ => ⟨hF, X, hX⟩⟩

theorem Formula.toTrivalent_forall (x : V) :
    (Formula.forall_ x φ).toTrivalent M g =
      Trivalent.forallWeak fun X => φ.toTrivalent M (Function.update g x X) :=
  SignType.eq_of_eq_zero_iff_of_eq_one_iff (by simp) <| by
    simp only [toTrivalent_eq_one_iff, felicitous_forall, realize_forall,
      Trivalent.forallWeak_eq_one_iff]
    exact ⟨fun ⟨hF, hT⟩ X => ⟨hF X, hT X⟩, fun h => ⟨fun X => (h X).1, fun X => (h X).2⟩⟩

theorem Formula.toTrivalent_surjective :
    Function.Surjective (Formula.toTrivalent M g : Formula V L P → SignType)
  | 0 => ⟨.presup .top (.neg .top), by simp⟩
  | -1 => ⟨.neg .top, by simp⟩
  | 1 => ⟨.top, by simp⟩

end Felicity

/-! ### Meanings -/

section Meanings

variable [DecidableEq V]

variable (α) in
/-- Two formulas are intersubstitutable, having the same meaning ((40)–(41) of
[abney-keshet-2025]), when they agree in truth and felicity in every model with atoms `α` under
every assignment and have the same local variables and label definitions. -/
def Formula.Intersubstitutable (φ ψ : Formula V L P) : Prop :=
  (∀ (M : Model P α) g, (Formula.Realize M g φ ↔ Formula.Realize M g ψ) ∧
    (φ.Felicitous M g ↔ ψ.Felicitous M g)) ∧
  (∀ x, x ∈ φ.locals ↔ x ∈ ψ.locals) ∧ ∀ d, d ∈ φ.defs ↔ d ∈ ψ.defs

namespace Formula.Intersubstitutable

variable {φ ψ χ : Formula V L P}

@[refl] protected theorem refl (φ : Formula V L P) : φ.Intersubstitutable α φ :=
  ⟨fun _ _ => ⟨Iff.rfl, Iff.rfl⟩, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

@[symm] protected theorem symm (h : φ.Intersubstitutable α ψ) : ψ.Intersubstitutable α φ :=
  ⟨fun M g => ⟨(h.1 M g).1.symm, (h.1 M g).2.symm⟩, fun x => (h.2.1 x).symm,
    fun d => (h.2.2 d).symm⟩

@[trans] protected theorem trans (h : φ.Intersubstitutable α ψ) (h' : ψ.Intersubstitutable α χ) :
    φ.Intersubstitutable α χ :=
  ⟨fun M g => ⟨(h.1 M g).1.trans (h'.1 M g).1, (h.1 M g).2.trans (h'.1 M g).2⟩,
    fun x => (h.2.1 x).trans (h'.2.1 x), fun d => (h.2.2 d).trans (h'.2.2 d)⟩

end Formula.Intersubstitutable

end Meanings

end PIP
