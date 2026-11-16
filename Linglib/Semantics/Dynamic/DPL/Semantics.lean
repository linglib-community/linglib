module

public import Linglib.Semantics.Dynamic.RegisterStructure
public import Linglib.Semantics.Dynamic.DPL.Syntax
public import Mathlib.ModelTheory.Semantics

/-!
# The interpretations of dynamic predicate logic

A formula of `DPL/Syntax.lean` has two interpretations in a structure `M`. The dynamic one,
`Formula.eval`, is Groenendijk and Stokhof's, a relation between assignments in the update
algebra of `Update.lean`: conjunction is composition, the existential a random reset followed by
its scope, and everything else a test, as in their translation into dynamic logic. The static
one is mathlib's satisfaction of the formula read as a first-order formula. A formula is true at
an assignment when it has an output there.
A list of conjuncts denotes [the product of its members](##DPL.Formula.eval_conjs), and an
existential closure [resets its variables and then interprets its
scope](##DPL.Formula.eval_exs). What a formula reads and changes is in `DPL/Context.lean`.

## Implementation notes

The clauses of `eval` are those of [groenendijk-stokhof-1991]'s translation of the logic into
quantificational dynamic logic, with `SetRel.dom` for the diamond at the true formula and
`SetRel.core` for the box, so the definition of the interpretation and the fact that the
translation preserves it coincide. `eval_neg_eq_antidomain`, `eval_imp_eq_dimp`,
`eval_disj_eq_dor` and `eval_all_eq_dimp` restate four clauses in the antidomain monoid of
updates, whose laws then apply.

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
  | rel R ts => test {g | Structure.RelMap R fun i ↦ (ts i).realize g}
  | equal t₁ t₂ => test {g | t₁.realize g = t₂.realize g}
  | neg φ => test (eval φ).domᶜ
  | conj φ ψ => eval φ ○ eval ψ
  | disj φ ψ => test ((eval φ).dom ∪ (eval ψ).dom)
  | imp φ ψ => test ((eval φ).core (eval ψ).dom)
  | ex x φ => randomAssign x ○ eval φ
  | all x φ => test ((randomAssign x).core (eval φ).dom)

variable (φ ψ : Formula L V) (x : V)

open scoped DPL

@[simp] theorem eval_top : (top : Formula L V).eval M = .id := rfl

@[simp] theorem eval_neg : (¬ᵈφ).eval M = test (φ.eval M).domᶜ := rfl

@[simp] theorem eval_conj : (φ ⋏ ψ).eval M = φ.eval M ○ ψ.eval M := rfl

@[simp] theorem eval_disj : (φ ⋎ ψ).eval M = test ((φ.eval M).dom ∪ (ψ.eval M).dom) := rfl

@[simp] theorem eval_imp : (φ ⟿ ψ).eval M = test ((φ.eval M).core (ψ.eval M).dom) := rfl

@[simp] theorem eval_ex : (∃[x] φ).eval M = randomAssign x ○ φ.eval M := rfl

@[simp] theorem eval_all :
    (∀[x] φ).eval M = test ((randomAssign x).core (φ.eval M).dom) := rfl

open AntidomainMonoid in
/-- Negation, implication, disjunction and the universal are the antidomain, the dynamic
implication and the dynamic disjunction of the monoid of updates. -/
theorem eval_neg_eq_antidomain : (¬ᵈφ).eval M = ∼(φ.eval M) := rfl

open AntidomainMonoid in
theorem eval_imp_eq_dimp : (φ ⟿ ψ).eval M = dimp (φ.eval M) (ψ.eval M) := (dimp_eq ..).symm

open AntidomainMonoid in
theorem eval_disj_eq_dor : (φ ⋎ ψ).eval M = dor (φ.eval M) (ψ.eval M) := (dor_eq ..).symm

open AntidomainMonoid in
theorem eval_all_eq_dimp : (∀[x] φ).eval M = dimp (randomAssign x) (φ.eval M) :=
  (dimp_eq ..).symm

@[simp] theorem eval_rel {n : ℕ} (R : L.Relations n) (ts : Fin n → L.Term V) :
    (rel R ts).eval M = test {g | Structure.RelMap R fun i ↦ (ts i).realize g} := rfl

@[simp] theorem eval_equal (t₁ t₂ : L.Term V) :
    (t₁ ≐ t₂).eval M = test {g | t₁.realize g = t₂.realize g} := rfl

/-- A conjunction of a list of formulas denotes the sequence of their interpretations. -/
theorem eval_conjs (φs : List (Formula L V)) : (conjs φs).eval M = (φs.map (eval M)).prod := by
  induction φs with
  | nil => rfl
  | cons φ φs ih => rw [conjs_cons, eval_conj, ih, List.map_cons, List.prod_cons, mul_def]

/-- An existential closure resets its variables one after another and then interprets its
scope. -/
theorem eval_exs (xs : List V) :
    (exs xs φ).eval M = (xs.map randomAssign).prod * φ.eval M := by
  induction xs with
  | nil => rw [exs_nil, List.map_nil, List.prod_nil, one_mul]
  | cons x xs ih =>
    rw [exs_cons, eval_ex, ih, List.map_cons, List.prod_cons, mul_assoc]
    rfl

theorem mem_eval_exs {xs : List V} {g h : V → M} :
    g ~[(exs xs φ).eval M] h ↔ ∃ k, (∀ y ∉ xs, k y = g y) ∧ k ~[φ.eval M] h := by
  rw [eval_exs, ← mul_one (List.prod _), one_def, ← test_univ, ← box_toFinset, mul_def]
  simp [mem_box_iff]

end DPL.Formula
