module

public import Linglib.Semantics.Dynamic.DRT.Assignment
public import Mathlib.ModelTheory.Semantics

/-!
# From DRT to predicate logic

The translation of a DRS `[U | γ₁, …, γₙ]` is the first-order formula `∃U (γ₁° ∧ ⋯ ∧ γₙ°)`,
where `(¬K)° = ¬K°`, `(K ∨ K')° = K° ∨ K'°` and `([U | γ⃗] ⇒ K')° = ∀U (γ₁° ∧ ⋯ ∧ γₙ° → K'°)`.
We define the translation as `DRS.toFormula` and `Condition.toFormula`.

An assignment realizes the translation of a condition exactly when it verifies the condition
(`Condition.realize_toFormula`), and that of a DRS exactly when it has an extension verifying the
DRS (`DRS.realize_toFormula`).

## TODO

The translation of a proper DRS has no free variables, so it is an `L.Sentence` and logical
consequence between proper DRSs is mathlib's `⊨ᵇ`. This needs `freeVarFinset` lemmas for
`relabel`, `iExs` and `iAlls`, which mathlib lacks.

## References

* [kamp-reyle-1993]
* [muskens-1996]
-/

@[expose] public section

open FirstOrder FirstOrder.Language
open SetRel

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w}

/-- Relabel the free referents `V` so that those in `U` move to the bound side
`{x // x ∈ U}` (and the rest stay free) — the splitting `iExs`/`iAlls` quantify
over. `DecidableEq V` is needed only for the `x ∈ U` test, not by `iExs`/`iAlls`. -/
def splitOn [DecidableEq V] (U : Finset V) : V → V ⊕ {x // x ∈ U} :=
  fun x => if h : x ∈ U then Sum.inr ⟨x, h⟩ else Sum.inl x

/-- Existentially close the referents in `U` within a formula over free
referents `V` (relabel via `splitOn`, then `Formula.iExs`). -/
noncomputable def closeExists [DecidableEq V] (U : Finset V) (φ : L.Formula V) : L.Formula V :=
  (φ.relabel (splitOn U)).iExs {x // x ∈ U}

/-- Universally close the referents in `U` (used for the antecedent of `⇒`). -/
noncomputable def closeForall [DecidableEq V] (U : Finset V) (φ : L.Formula V) : L.Formula V :=
  (φ.relabel (splitOn U)).iAlls {x // x ∈ U}

section Translation

variable [DecidableEq V]

mutual
/-- The translation of a DRS existentially closes its universe over the conjunction of its
translated conditions (§1.5). -/
noncomputable def DRS.toFormula : DRS L V → L.Formula V
  | ⟨U, cs⟩ => closeExists U (Condition.toFormulaAll cs)
/-- The translation of a condition closes the universe of each sub-box existentially over the
conjunction of its translated conditions, and that of the antecedent of a `⇒` universally (§1.5).
-/
noncomputable def Condition.toFormula : Condition L V → L.Formula V
  | .atom a => a.toFormula
  | .eq a b => Term.equal (Term.var a) (Term.var b)
  | .neg K => (DRS.toFormula K).not
  | .imp ⟨Ua, ca⟩ c => closeForall Ua ((Condition.toFormulaAll ca).imp (DRS.toFormula c))
  | .dis l r => DRS.toFormula l ⊔ DRS.toFormula r
/-- The conjunction of a list of translated conditions. -/
noncomputable def Condition.toFormulaAll : List (Condition L V) → L.Formula V
  | [] => ⊤
  | c :: cs => Condition.toFormula c ⊓ Condition.toFormulaAll cs
end

theorem DRS.toFormula_eq (K : DRS L V) :
    K.toFormula = closeExists K.referents (Condition.toFormulaAll K.conditions) := by
  cases K; rfl

theorem Condition.toFormulaAll_nil :
    Condition.toFormulaAll ([] : List (Condition L V)) = ⊤ := rfl

theorem Condition.toFormulaAll_cons (c : Condition L V) (cs : List (Condition L V)) :
    Condition.toFormulaAll (c :: cs) = Condition.toFormula c ⊓ Condition.toFormulaAll cs := rfl

theorem Condition.toFormula_neg (K : DRS L V) :
    Condition.toFormula (.neg K) = (DRS.toFormula K).not := rfl

theorem Condition.toFormula_imp (a c : DRS L V) :
    Condition.toFormula (.imp a c) =
      closeForall a.referents ((Condition.toFormulaAll a.conditions).imp (DRS.toFormula c)) := by
  cases a; rfl

theorem Condition.toFormula_dis (l r : DRS L V) :
    Condition.toFormula (.dis l r) = DRS.toFormula l ⊔ DRS.toFormula r := rfl

end Translation

variable {M : Type x} [L.Structure M]

/-! ### Correctness of the translation -/

private theorem elim_comp_splitOn [DecidableEq V] (U : Finset V) (v : V → M)
    (i : {x // x ∈ U} → M) : (Sum.elim v i) ∘ (splitOn U) = Function.updateFinset v U i := by
  funext x
  simp only [splitOn, Function.updateFinset, Function.comp_apply]
  by_cases h : x ∈ U <;> simp [h]

theorem realize_closeExists [DecidableEq V] (U : Finset V) (φ : L.Formula V) (v : V → M) :
    (closeExists U φ).Realize v ↔ ∃ v', (∀ x ∉ U, v' x = v x) ∧ φ.Realize v' := by
  rw [closeExists, Formula.realize_iExs]
  simp only [Formula.realize_relabel, elim_comp_splitOn]
  simp only [← Function.mem_range_updateFinset_iff, Set.exists_range_iff]

theorem realize_closeForall [DecidableEq V] (U : Finset V) (φ : L.Formula V) (v : V → M) :
    (closeForall U φ).Realize v ↔ ∀ v', (∀ x ∉ U, v' x = v x) → φ.Realize v' := by
  rw [closeForall, Formula.realize_iAlls]
  simp only [Formula.realize_relabel, elim_comp_splitOn]
  simp only [← Function.mem_range_updateFinset_iff, Set.forall_mem_range]

private theorem Condition.realize_toFormulaAll_of_forall [DecidableEq V]
    {cs : List (Condition L V)} {v : V → M}
    (ih : ∀ c ∈ cs, (Condition.toFormula c).Realize v ↔ v ⊨[.assignment M] c) :
    (Condition.toFormulaAll cs).Realize v ↔ v ∈ Condition.verifiersAll (.assignment M) cs := by
  induction cs with
  | nil => simp [Condition.toFormulaAll_nil, Formula.realize_top]
  | cons c cs ihl =>
    rw [Condition.toFormulaAll_cons, Formula.realize_inf, Condition.mem_verifiersAll_cons]
    exact and_congr (ih c (by simp)) (ihl fun d hd => ih d (List.mem_cons_of_mem c hd))

private theorem DRS.realize_toFormulaAll_of_forall [DecidableEq V] {K : DRS L V} {v : V → M}
    (ih : ∀ c ∈ K.conditions, ∀ w : V → M,
      (Condition.toFormula c).Realize w ↔ w ⊨[.assignment M] c) :
    (Condition.toFormulaAll K.conditions).Realize v ↔ v ⊨[.assignment M] K :=
  Condition.realize_toFormulaAll_of_forall fun c hc => ih c hc v

private theorem DRS.realize_toFormula_of_forall [DecidableEq V] {K : DRS L V}
    {v : V → M}
    (ih : ∀ c ∈ K.conditions, ∀ w : V → M,
      (Condition.toFormula c).Realize w ↔ w ⊨[.assignment M] c) :
    (DRS.toFormula K).Realize v ↔ v ∈ (K.eval (.assignment M)).dom := by
  rw [DRS.toFormula_eq, realize_closeExists, DRS.mem_dom_eval_assignment]
  exact exists_congr fun v' => and_congr_right fun _ => DRS.realize_toFormulaAll_of_forall ih

/-- An assignment realizes the translation of a condition iff it verifies the condition. -/
theorem Condition.realize_toFormula [DecidableEq V] (c : Condition L V) (v : V → M) :
    (Condition.toFormula c).Realize v ↔ v ⊨[.assignment M] c := by
  induction c generalizing v with
  | atom a => simp [Condition.toFormula]
  | eq a b => simp [Condition.toFormula, Formula.realize_equal]
  | neg K ih =>
    rw [Condition.toFormula_neg, Formula.realize_not, DRS.realize_toFormula_of_forall ih,
      Condition.verifiers_neg, Set.mem_compl_iff]
  | imp a c iha ihc =>
    rw [Condition.toFormula_imp, Condition.mem_verifiers_assignment_imp, realize_closeForall]
    refine forall_congr' fun v' => imp_congr_right fun _ => ?_
    rw [Formula.realize_imp, DRS.realize_toFormulaAll_of_forall iha,
      DRS.realize_toFormula_of_forall ihc]
  | dis l r ihl ihr =>
    rw [Condition.toFormula_dis, Formula.realize_sup, Condition.verifiers_dis, Set.mem_union,
      DRS.realize_toFormula_of_forall ihl, DRS.realize_toFormula_of_forall ihr]

theorem Condition.realize_toFormulaAll [DecidableEq V] (cs : List (Condition L V))
    (v : V → M) :
    (Condition.toFormulaAll cs).Realize v ↔ v ∈ Condition.verifiersAll (.assignment M) cs :=
  Condition.realize_toFormulaAll_of_forall fun c _ => Condition.realize_toFormula c v

/-- An assignment realizes the translation of a DRS iff it has an extension verifying the DRS
(§1.5). -/
theorem DRS.realize_toFormula [DecidableEq V] (K : DRS L V) (v : V → M) :
    (K.toFormula).Realize v ↔ v ∈ (K.eval (.assignment M)).dom :=
  DRS.realize_toFormula_of_forall fun c _ w => Condition.realize_toFormula c w

/-- The translation of a proper DRS is realized iff some assignment verifies the DRS. -/
theorem DRS.realize_toFormula_of_isProper [DecidableEq V] {K : DRS L V} (hK : K.IsProper)
    (v : V → M) : K.toFormula.Realize v ↔ ∃ f : V → M, f ⊨[.assignment M] K := by
  rw [DRS.realize_toFormula, DRS.mem_dom_eval_assignment_iff_of_isProper hK]

end DRT
