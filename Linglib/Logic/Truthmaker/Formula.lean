module

public import Linglib.Logic.Truthmaker.Bilateral

/-!
# Formulas of propositional truthmaker semantics

Formulas are built from sentence letters by negation, conjunction and disjunction. A valuation `V`
assigns each letter a bilateral proposition, and `φ.denote V` extends it to formulas by the
propositional operations: negation swaps verifiers and falsifiers, a conjunction is verified by the
fusions of verifiers of its conjuncts and falsified by the falsifiers of either, and dually for a
disjunction. `φ.Realize v` is truth under a classical valuation `v`.

If the letters denote propositions that are exclusive and exhaustive over the possible states,
so does every formula (`Truthmaker.Formula.exclusive_denote`,
`Truthmaker.Formula.exhaustive_denote`), and a formula is true at a world exactly when it is
realized by the valuation making a letter true when the world contains one of its verifiers
(`Truthmaker.Formula.mem_upperClosure_pro_denote_iff`).

## References

* [K. Fine, *A Theory of Truthmaker Content I: Conjunction, Disjunction and Negation*
  (2017)][fine-2017a]
-/

@[expose] public section

open SetFamily
open scoped Bilattice

namespace Truthmaker

/-- The formulas of a propositional language over sentence letters `A`. -/
inductive Formula (A : Type*)
  | atom (a : A)
  | neg (φ : Formula A)
  | conj (φ ψ : Formula A)
  | disj (φ ψ : Formula A)

namespace Formula

variable {A S : Type*}

/-- A formula is realized by a valuation when the classical truth tables make it true. -/
def Realize (v : A → Prop) : Formula A → Prop
  | atom a => v a
  | neg φ => ¬ φ.Realize v
  | conj φ ψ => φ.Realize v ∧ ψ.Realize v
  | disj φ ψ => φ.Realize v ∨ ψ.Realize v

@[simp] theorem realize_atom (v : A → Prop) (a : A) : (atom a).Realize v ↔ v a := Iff.rfl

@[simp] theorem realize_neg (v : A → Prop) (φ : Formula A) :
    (neg φ).Realize v ↔ ¬ φ.Realize v := Iff.rfl

@[simp] theorem realize_conj (v : A → Prop) (φ ψ : Formula A) :
    (conj φ ψ).Realize v ↔ φ.Realize v ∧ ψ.Realize v := Iff.rfl

@[simp] theorem realize_disj (v : A → Prop) (φ ψ : Formula A) :
    (disj φ ψ).Realize v ↔ φ.Realize v ∨ ψ.Realize v := Iff.rfl

variable [SemilatticeSup S] {V : A → Set S ⊙ Set S} {P : LowerSet S}

/-- The bilateral proposition a formula expresses when `V` assigns one to each sentence letter. -/
def denote (V : A → Set S ⊙ Set S) : Formula A → Set S ⊙ Set S
  | atom a => V a
  | neg φ => (φ.denote V)ᶜ
  | conj φ ψ => Truthmaker.conj (φ.denote V) (ψ.denote V)
  | disj φ ψ => Truthmaker.disj (φ.denote V) (ψ.denote V)

@[simp] theorem denote_atom (V : A → Set S ⊙ Set S) (a : A) : (atom a).denote V = V a := rfl

@[simp] theorem denote_neg (V : A → Set S ⊙ Set S) (φ : Formula A) :
    (neg φ).denote V = (φ.denote V)ᶜ := rfl

@[simp] theorem denote_conj (V : A → Set S ⊙ Set S) (φ ψ : Formula A) :
    (conj φ ψ).denote V = Truthmaker.conj (φ.denote V) (ψ.denote V) := rfl

@[simp] theorem denote_disj (V : A → Set S ⊙ Set S) (φ ψ : Formula A) :
    (disj φ ψ).denote V = Truthmaker.disj (φ.denote V) (ψ.denote V) := rfl

theorem exclusive_denote (hV : ∀ a, Exclusive P (V a)) (φ : Formula A) :
    Exclusive P (φ.denote V) := by
  induction φ with
  | atom a => exact hV a
  | neg φ ih => exact ih.compl
  | conj φ ψ ihφ ihψ => exact ihφ.conj ihψ
  | disj φ ψ ihφ ihψ => exact ihφ.disj ihψ

theorem exhaustive_denote (hV : ∀ a, Exhaustive P (V a)) (φ : Formula A) :
    Exhaustive P (φ.denote V) := by
  induction φ with
  | atom a => exact hV a
  | neg φ ih => exact ih.compl
  | conj φ ψ ihφ ihψ => exact ihφ.conj ihψ
  | disj φ ψ ihφ ihψ => exact ihφ.disj ihψ

/-- A world contains a falsifier of a formula over exclusive and exhaustive letters exactly when it
contains no verifier of it. -/
theorem mem_upperClosure_con_denote_iff (hV : ∀ a, Exclusive P (V a))
    (hV' : ∀ a, Exhaustive P (V a)) {w : S} (hw : Maximal (· ∈ P) w) (φ : Formula A) :
    w ∈ upperClosure (φ.denote V).con ↔ w ∉ upperClosure (φ.denote V).pro :=
  ⟨fun hc hp ↦ exclusive_iff.1 (exclusive_denote hV φ) w hw.prop hp hc,
    ((exhaustive_denote hV' φ).mem_upperClosure hw).resolve_left⟩

/-- A formula over exclusive and exhaustive letters is true at a world exactly when it is realized
by the valuation making a letter true when the world contains one of its verifiers. -/
theorem mem_upperClosure_pro_denote_iff (hV : ∀ a, Exclusive P (V a))
    (hV' : ∀ a, Exhaustive P (V a)) {w : S} (hw : Maximal (· ∈ P) w) (φ : Formula A) :
    w ∈ upperClosure (φ.denote V).pro ↔ φ.Realize fun a ↦ w ∈ upperClosure (V a).pro := by
  induction φ with
  | atom a => rfl
  | neg φ ih =>
    rw [denote_neg, Bilattice.Product.pro_compl, mem_upperClosure_con_denote_iff hV hV' hw, ih,
      realize_neg]
  | conj φ ψ ihφ ihψ =>
    rw [denote_conj, pro_conj, upperClosure_sups, UpperSet.mem_sup_iff, ihφ, ihψ, realize_conj]
  | disj φ ψ ihφ ihψ =>
    rw [denote_disj, pro_disj, upperClosure_union, UpperSet.mem_inf_iff, ihφ, ihψ, realize_disj]

end Formula

end Truthmaker
