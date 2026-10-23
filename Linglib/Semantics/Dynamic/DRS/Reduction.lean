module

public import Linglib.Semantics.Dynamic.DRS.Verification
public import Mathlib.ModelTheory.Semantics

/-!
# From DRT to predicate logic

This file translates each DRS into a `FirstOrder.Language.Formula` and proves that the
translation is realized exactly when the DRS is verified, Kamp and Reyle's reduction of the DRS
language to first-order logic in §1.5, also given by Muskens. The universe of a sub-DRS is
existentially closed (`closeExists`, via `Formula.iExs`), and the antecedent of a `⇒` universally
(`closeForall`, via `Formula.iAlls`). The translation of a proper DRS realizes the same way under
every assignment, as truth in the model (p. 138).

## Main declarations

* `DRS.toFormula`, `Condition.toFormula`: the translation into `L.Formula V`.
* `DRS.realize_toFormula`: truth of a DRS matches its first-order
  translation's `Realize`.
* `DRS.realize_toFormula_of_isProper`: the translation of a proper DRS is realized
  iff some embedding verifies the DRS.

## TODO

The translation of a proper DRS is closed (p. 138), so it is an `L.Sentence` and
Def. 1.4.6's logical consequence is mathlib's `⊨ᵇ`; this needs `freeVarFinset`
lemmas for `relabel`, `iExs` and `iAlls`, which mathlib lacks.

## References

* [kamp-reyle-1993]
* [muskens-1996]
-/

@[expose] public section

open FirstOrder FirstOrder.Language

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

/-! ### Agreement of the translation with the bespoke semantics -/

/-- The assignment that agrees with `v` off `U` and is given by `i` on `U`. -/
private def extendOn [DecidableEq V] (U : Finset V) (v : V → M) (i : {x // x ∈ U} → M) : V → M :=
  fun x => if h : x ∈ U then i ⟨x, h⟩ else v x

private theorem elim_comp_splitOn [DecidableEq V] (U : Finset V) (v : V → M)
    (i : {x // x ∈ U} → M) : (Sum.elim v i) ∘ (splitOn U) = extendOn U v i := by
  funext x
  simp only [splitOn, extendOn, Function.comp_apply]
  by_cases h : x ∈ U <;> simp [h]

private theorem extendOn_agrees [DecidableEq V] (U : Finset V) (v : V → M)
    (i : {x // x ∈ U} → M) : ∀ x ∉ U, extendOn U v i x = v x := by
  intro x hx; simp only [extendOn, dite_eq_right hx]

private theorem extendOn_restrict [DecidableEq V] (U : Finset V) (v v' : V → M)
    (h : ∀ x ∉ U, v' x = v x) : extendOn U v (fun s => v' s.val) = v' := by
  funext x
  simp only [extendOn]
  by_cases hx : x ∈ U
  · simp [hx]
  · simp [hx, h x hx]

private theorem exists_extend_iff [DecidableEq V] (U : Finset V) (v : V → M)
    (P : (V → M) → Prop) :
    (∃ i : {x // x ∈ U} → M, P (extendOn U v i)) ↔
      ∃ v', (∀ x ∉ U, v' x = v x) ∧ P v' := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨extendOn U v i, extendOn_agrees U v i, hi⟩
  · rintro ⟨v', hagree, hv'⟩
    refine ⟨fun s => v' s.val, ?_⟩
    rw [extendOn_restrict U v v' hagree]; exact hv'

private theorem forall_extend_iff [DecidableEq V] (U : Finset V) (v : V → M)
    (P : (V → M) → Prop) :
    (∀ i : {x // x ∈ U} → M, P (extendOn U v i)) ↔
      ∀ v', (∀ x ∉ U, v' x = v x) → P v' := by
  constructor
  · intro hi v' hagree
    have := hi (fun s => v' s.val)
    rwa [extendOn_restrict U v v' hagree] at this
  · intro hv' i
    exact hv' (extendOn U v i) (extendOn_agrees U v i)

theorem realize_closeExists [DecidableEq V] (U : Finset V) (φ : L.Formula V) (v : V → M) :
    (closeExists U φ).Realize v ↔ ∃ v', (∀ x ∉ U, v' x = v x) ∧ φ.Realize v' := by
  rw [closeExists, Formula.realize_iExs]
  simp only [Formula.realize_relabel, elim_comp_splitOn]
  exact exists_extend_iff U v (Formula.Realize φ)

theorem realize_closeForall [DecidableEq V] (U : Finset V) (φ : L.Formula V) (v : V → M) :
    (closeForall U φ).Realize v ↔ ∀ v', (∀ x ∉ U, v' x = v x) → φ.Realize v' := by
  rw [closeForall, Formula.realize_iAlls]
  simp only [Formula.realize_relabel, elim_comp_splitOn]
  exact forall_extend_iff U v (Formula.Realize φ)

private theorem Condition.realize_toFormulaAll_of_forall [DecidableEq V]
    {cs : List (Condition L V)} {v : V → M}
    (ih : ∀ c ∈ cs, (Condition.toFormula c).Realize v ↔ VerifiesCondition v c) :
    (Condition.toFormulaAll cs).Realize v ↔ ∀ c ∈ cs, VerifiesCondition v c := by
  induction cs with
  | nil => simp [Condition.toFormulaAll_nil, Formula.realize_top]
  | cons c cs ihl =>
    rw [Condition.toFormulaAll_cons, Formula.realize_inf, List.forall_mem_cons]
    exact and_congr (ih c (by simp)) (ihl fun d hd => ih d (List.mem_cons_of_mem c hd))

private theorem DRS.realize_toFormula_of_forall [DecidableEq V] {K : DRS L V}
    {v : V → M}
    (ih : ∀ c ∈ K.conditions, ∀ w : V → M,
      (Condition.toFormula c).Realize w ↔ VerifiesCondition w c) :
    (DRS.toFormula K).Realize v ↔ ∃ v', K.Extends v v' ∧ Verifies v' K := by
  simp only [DRS.toFormula_eq, realize_closeExists, Box.Extends, verifies_iff]
  exact exists_congr fun v' => and_congr_right fun _ =>
    Condition.realize_toFormulaAll_of_forall fun c hc => ih c hc v'

/-- A single condition's translation realizes as `VerifiesCondition`. -/
theorem Condition.realize_toFormula [DecidableEq V] (c : Condition L V) (v : V → M) :
    (Condition.toFormula c).Realize v ↔ VerifiesCondition v c := by
  induction c generalizing v with
  | atom a => simp [Condition.toFormula]
  | eq a b => simp [Condition.toFormula, Formula.realize_equal]
  | neg K ih =>
    rw [Condition.toFormula_neg, Formula.realize_not, DRS.realize_toFormula_of_forall ih,
      verifies_neg]
  | imp a c iha ihc =>
    rw [Condition.toFormula_imp, verifies_imp, realize_closeForall]
    refine forall_congr' fun v' => imp_congr_right fun _ => ?_
    rw [Formula.realize_imp, Condition.realize_toFormulaAll_of_forall fun d hd => iha d hd v',
      DRS.realize_toFormula_of_forall ihc, verifies_iff]
  | dis l r ihl ihr =>
    rw [Condition.toFormula_dis, Formula.realize_sup, verifies_dis,
      DRS.realize_toFormula_of_forall ihl, DRS.realize_toFormula_of_forall ihr]

theorem Condition.realize_toFormulaAll [DecidableEq V] (cs : List (Condition L V))
    (v : V → M) :
    (Condition.toFormulaAll cs).Realize v ↔ ∀ c ∈ cs, VerifiesCondition v c :=
  Condition.realize_toFormulaAll_of_forall fun c _ => Condition.realize_toFormula c v

/-- The translation's `Realize` coincides with verification (§1.5). As `toFormula`
existentially closes the universe, the correspondence is with an embedding `v'`
extending `v` over `K.referents`. -/
theorem DRS.realize_toFormula [DecidableEq V] (K : DRS L V) (v : V → M) :
    (K.toFormula).Realize v ↔ ∃ v', K.Extends v v' ∧ Verifies v' K :=
  DRS.realize_toFormula_of_forall fun c _ w => Condition.realize_toFormula c w

/-- The translation of a proper DRS is realized under any assignment iff some embedding
verifies the DRS (p. 138, Def. 1.4.5). -/
theorem DRS.realize_toFormula_of_isProper [DecidableEq V] {K : DRS L V} (hK : K.IsProper)
    (v : V → M) : K.toFormula.Realize v ↔ ∃ f : V → M, Verifies f K := by
  rw [DRS.realize_toFormula, exists_extends_verifies_iff_of_isProper hK]

end DRT
