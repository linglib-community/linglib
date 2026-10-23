module

public import Linglib.Semantics.Dynamic.RegisterStructure
public import Linglib.Semantics.Dynamic.DPL.Syntax
public import Mathlib.ModelTheory.Semantics

/-!
# The interpretations of dynamic predicate logic

A formula of `DPL/Syntax.lean` has two interpretations in a structure `M`. The dynamic one,
`Formula.eval`, is Groenendijk and Stokhof's, a relation between assignments, built from the
update algebra of `Update.lean`, with conjunction as composition, the existential as a random
reset followed by its scope, and everything else a test. The static one is that of predicate
logic, mathlib's satisfaction of the formula read as a first-order formula,
`φ.toFormula.Realize`. A formula is true at an assignment under the dynamic interpretation when
it has an output there, `(φ.eval M).dom`; the two notions of truth agree on the scope-bound
formulas (`DPL/Context.lean`) and differ where a quantifier binds outside its scope.

## Main definitions

* `DPL.Formula.eval`: the dynamic interpretation.

## Main results

* `DPL.Formula.isTest_eval`: a formula with no active quantifier variable is a test.

## Implementation notes

`eval` is stated through the substrate's `dexists` and `dforall`, so that the laws of the update
algebra apply to it as they stand; `mem_dexists` and `mem_dforall` unfold them at assignments.
The converse of `isTest_eval` fails, a test such as `x ≐ y ⋏ ∃[x] (x ≐ y)` having an active
quantifier variable.

## References

* [groenendijk-stokhof-1991]
-/

@[expose] public section

open FirstOrder FirstOrder.Language DynamicSemantics Update SetRel

namespace DPL.Formula

universe u v w x

variable {L : Language.{u, v}} {V : Type w} [DecidableEq V] (M : Type x) [L.Structure M]

/-- The dynamic interpretation relates the input assignments to their output assignments. -/
def eval : Formula L V → Update (V → M)
  | top => .id
  | rel R ts => test {g | Structure.RelMap R fun i => (ts i).realize g}
  | equal t₁ t₂ => test {g | t₁.realize g = t₂.realize g}
  | neg φ => test (Update.neg (eval φ))
  | conj φ ψ => eval φ ○ eval ψ
  | disj φ ψ => test (Update.disj (eval φ) (eval ψ))
  | imp φ ψ => test (impl (eval φ) (eval ψ))
  | ex x φ => dexists x (eval φ)
  | all x φ => test (dforall x (eval φ))

variable (φ ψ : Formula L V) (x : V)

open scoped DPL

@[simp] theorem eval_top : (top : Formula L V).eval M = .id := rfl

@[simp] theorem eval_neg : (¬ᵈφ).eval M = test (Update.neg (φ.eval M)) := rfl

@[simp] theorem eval_conj : (φ ⋏ ψ).eval M = φ.eval M ○ ψ.eval M := rfl

@[simp] theorem eval_disj : (φ ⋎ ψ).eval M = test (Update.disj (φ.eval M) (ψ.eval M)) := rfl

@[simp] theorem eval_imp : (φ ⟿ ψ).eval M = test (impl (φ.eval M) (ψ.eval M)) := rfl

@[simp] theorem eval_ex : (∃[x] φ).eval M = dexists x (φ.eval M) := rfl

@[simp] theorem eval_all : (∀[x] φ).eval M = test (dforall x (φ.eval M)) := rfl

@[simp] theorem eval_rel {n : ℕ} (R : L.Relations n) (ts : Fin n → L.Term V) :
    (rel R ts).eval M = test {g | Structure.RelMap R fun i => (ts i).realize g} := rfl

@[simp] theorem eval_equal (t₁ t₂ : L.Term V) :
    (t₁ ≐ t₂).eval M = test {g | t₁.realize g = t₂.realize g} := rfl

theorem mem_eval_exs {xs : List V} {g h : V → M} :
    g ~[(exs xs φ).eval M] h ↔ ∃ k, (∀ y ∉ xs, k y = g y) ∧ k ~[φ.eval M] h := by
  induction xs generalizing g with
  | nil => exact ⟨fun hgh ↦ ⟨g, fun _ _ ↦ rfl, hgh⟩,
      fun ⟨k, hk, hkh⟩ ↦ (funext fun y ↦ hk y List.not_mem_nil : k = g) ▸ hkh⟩
  | cons x xs ih =>
    rw [exs_cons, eval_ex, mem_dexists]
    simp only [RegisterStructure.extend_eq_update]
    constructor
    · rintro ⟨e, he⟩
      obtain ⟨k, hk, hkh⟩ := ih.mp he
      refine ⟨k, fun y hy ↦ ?_, hkh⟩
      have hyx : y ≠ x := fun h ↦ hy (by simp [h])
      rw [hk y fun h ↦ hy (List.mem_cons_of_mem _ h), Function.update_of_ne hyx]
    · rintro ⟨k, hk, hkh⟩
      refine ⟨k x, ih.mpr ⟨k, fun y hy ↦ ?_, hkh⟩⟩
      obtain rfl | hyx := eq_or_ne y x
      · rw [Function.update_self]
      · rw [Function.update_of_ne hyx, hk y (by simp [hyx, hy])]

theorem eval_conjs_map {α : Type*} (t : α → Formula L V) (C : α → Set (V → M)) (as : List α)
    (h : ∀ a ∈ as, (t a).eval M = test (C a)) :
    (conjs (as.map t)).eval M = test {f | ∀ a ∈ as, f ∈ C a} := by
  induction as with
  | nil => simp
  | cons a as ih =>
    rw [List.map_cons, conjs_cons, eval_conj, h a List.mem_cons_self,
      ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb), test_comp_test]
    exact congrArg test (Set.ext fun f ↦ by simp)

variable {φ} in
/-- A formula with no active quantifier variable is a test, since atoms, negations,
disjunctions, implications and universals are and conjunction preserves it. -/
theorem isTest_eval (h : φ.aqv = ∅) : IsTest (φ.eval M) := by
  induction φ with
  | top => exact subset_rfl
  | conj φ ψ ihφ ihψ =>
    rw [aqv_conj, Finset.union_eq_empty] at h
    exact (ihφ h.1).comp (ihψ h.2)
  | ex x φ => exact absurd h (Finset.insert_ne_empty _ _)
  | _ => exact isTest_test _

end DPL.Formula
