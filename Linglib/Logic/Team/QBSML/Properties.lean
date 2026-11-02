module

public import Linglib.Logic.Team.QBSML.Defs
public import Linglib.Logic.Team.Closure
public import Linglib.Logic.Team.Definability

/-!
# QBSML formula properties

This file proves that the support of a QBSML formula is closed under unions, and, when the
formula is `NE`-free, downward closed and contains the empty state. An `NE`-free formula is
therefore flat, as in `Logic/Team/BSML/Properties.lean`, and a state supports it iff its
translation is classically satisfied at every index of the state.

## Main declarations

* `supClosed_support`, `support_empty_of_neFree`, `isLowerSet_support_of_neFree`: the closure
  properties.
* `isFlat_support_of_neFree`: `NE`-free formulas are flat.
* `Formula.toModal`, `support_iff_forall_realize`: Aloni and van Ormondt's Proposition 4.1, a
  state supports an `NE`-free formula iff its modal translation holds at every index.
* `eval_mapAtoms_iff`: replacing atoms by bilaterally equivalent formulas preserves support.

## Implementation notes

Each closure property is proved for both polarities by induction on the formula, each case the
lemma of its operation in `Team/Operations.lean`. The quantifier cases are those of the box and
the lax diamond of modal inclusion logic, both of which preserve union closure; the strict
diamond does not ([anttila-haggblom-yang-2025] p. 759).

## References

* [aloni-vanormondt-2023] Aloni and van Ormondt, Modified Numerals and Split Disjunction: The
  First-Order Case
* [anttila-2021] Anttila, The Logic of Free Choice: Axiomatizations of State-based Modal Logics
* [anttila-haggblom-yang-2025] Anttila, Häggblom and Yang, Axiomatizing modal inclusion logic
  and its variants
-/

@[expose] public section

namespace QBSML

open Team

variable {W Var Domain Const Pred : Type*}

section Closure

variable [DecidableEq W] [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain]

/-! ### Closure properties by induction over the connectives

Each case is the closure lemma of its operation from `Team/Operations.lean`, and negation swaps
the two polarities. -/

private theorem support_and_antiSupport_supClosed (φ : Formula Var Const Pred)
    (M : Model W Domain Const Pred) :
    SupClosed {s | support M φ s} ∧ SupClosed {s | antiSupport M φ s} := by
  induction φ with
  | pred P x => exact ⟨supClosed_flat _, supClosed_flat _⟩
  | predc P c => exact ⟨supClosed_flat _, supClosed_flat _⟩
  | ne => exact ⟨supClosed_ne, supClosed_singleton_empty⟩
  | neg _ ih => exact ih.symm
  | conj _ _ ih₁ ih₂ => exact ⟨ih₁.1.inter ih₂.1, ih₁.2.tensor ih₂.2⟩
  | disj _ _ ih₁ ih₂ => exact ⟨ih₁.1.tensor ih₂.1, ih₁.2.inter ih₂.2⟩
  | poss _ _ => exact ⟨supClosed_flat _, supClosed_flat _⟩
  | exi x _ ih => exact ⟨ih.1.possLax, ih.2.necImage⟩
  | univ x _ ih => exact ⟨ih.1.necImage, ih.2.possLax⟩

/-- QBSML support is union closed, as BSML's is ([anttila-2021] Proposition 2.2.8).
    [aloni-vanormondt-2023] Fact 2 states this for `NE`-free quantified formulas, but its argument
    does not use the hypothesis. -/
theorem supClosed_support (M : Model W Domain Const Pred) (φ : Formula Var Const Pred) :
    SupClosed {s : Finset (Index W Var Domain) | support M φ s} :=
  (support_and_antiSupport_supClosed φ M).1

private theorem support_and_antiSupport_empty_of_neFree
    {φ : Formula Var Const Pred} (hNE : φ.NEFree)
    (M : Model W Domain Const Pred) :
    support M φ (∅ : Finset (Index W Var Domain)) ∧
    antiSupport M φ (∅ : Finset (Index W Var Domain)) := by
  induction hNE with
  | pred P x => exact ⟨empty_mem_flat _, empty_mem_flat _⟩
  | predc P c => exact ⟨empty_mem_flat _, empty_mem_flat _⟩
  | neg _ ih => exact ih.symm
  | conj _ _ ih₁ ih₂ => exact ⟨⟨ih₁.1, ih₂.1⟩, empty_mem_tensor ih₁.2 ih₂.2⟩
  | disj _ _ ih₁ ih₂ => exact ⟨empty_mem_tensor ih₁.1 ih₂.1, ⟨ih₁.2, ih₂.2⟩⟩
  | poss _ _ => exact ⟨empty_mem_flat _, empty_mem_flat _⟩
  | exi x _ ih => exact ⟨empty_mem_possLax ih.1, empty_mem_necImage ih.2⟩
  | univ x _ ih => exact ⟨empty_mem_necImage ih.1, empty_mem_possLax ih.2⟩

theorem support_empty_of_neFree {φ : Formula Var Const Pred}
    (hNE : φ.NEFree) (M : Model W Domain Const Pred) :
    support M φ ∅ :=
  (support_and_antiSupport_empty_of_neFree hNE M).1

private theorem support_and_antiSupport_isLowerSet_of_neFree
    {φ : Formula Var Const Pred} (hNE : φ.NEFree) (M : Model W Domain Const Pred) :
    IsLowerSet {s | support M φ s} ∧ IsLowerSet {s | antiSupport M φ s} := by
  induction hNE with
  | pred P x => exact ⟨isLowerSet_flat _, isLowerSet_flat _⟩
  | predc P c => exact ⟨isLowerSet_flat _, isLowerSet_flat _⟩
  | neg _ ih => exact ih.symm
  | conj _ _ ih₁ ih₂ => exact ⟨ih₁.1.inter ih₂.1, ih₁.2.tensor ih₂.2⟩
  | disj _ _ ih₁ ih₂ => exact ⟨ih₁.1.tensor ih₂.1, ih₁.2.inter ih₂.2⟩
  | poss _ _ => exact ⟨isLowerSet_flat _, isLowerSet_flat _⟩
  | exi x _ ih => exact ⟨ih.1.possLax, ih.2.necImage⟩
  | univ x _ ih => exact ⟨ih.1.necImage, ih.2.possLax⟩

/-- `NE`-free QBSML formulas are downward closed ([aloni-vanormondt-2023] Fact 2,
    [anttila-2021] Proposition 2.2.8). -/
theorem isLowerSet_support_of_neFree {φ : Formula Var Const Pred}
    (hNE : φ.NEFree) (M : Model W Domain Const Pred) :
    IsLowerSet { t : Finset (Index W Var Domain) | support M φ t } :=
  (support_and_antiSupport_isLowerSet_of_neFree hNE M).1

/-! ### Flatness corollary -/

/-- NE-free QBSML formulas are flat, as BSML's are ([anttila-2021] Corollary 2.2.9). -/
theorem isFlat_support_of_neFree {φ : Formula Var Const Pred}
    (hNE : φ.NEFree) (M : Model W Domain Const Pred) :
    IsFlat { t : Finset (Index W Var Domain) | support M φ t } :=
  isFlat_of_isLowerSet_supClosed_empty
    (isLowerSet_support_of_neFree hNE M)
    (supClosed_support M φ)
    (support_empty_of_neFree hNE M)

/-! ### Soundness for the flat cell (Definability bridge) -/

/-- Every team property defined by an NE-free QBSML formula is flat, as in
    [aloni-vanormondt-2023]'s reduction of NE-free QBSML to classical first-order modal logic. -/
theorem definableClass_support_neFree_subset (M : Model W Domain Const Pred) :
    definableClass (fun φ : {φ : Formula Var Const Pred // φ.NEFree} ↦ support M φ.1) ⊆
      {P | IsFlat P} :=
  definableClass_subset fun φ ↦ isFlat_support_of_neFree φ.2 M

end Closure

/-! ### Fact 1: classical validities

[aloni-vanormondt-2023] Fact 1 lists the classical equivalences QBSML validates: double negation
elimination, the De Morgan laws, and the `□`/`◇` and `∀`/`∃` dualities. Each holds by `Iff.rfl`,
since negation swaps `support` and `antiSupport`, whose clauses are De Morgan duals. -/

section Fact1

variable [DecidableEq W] [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain]
variable (M : Model W Domain Const Pred) (φ ψ : Formula Var Const Pred)
  (x : Var) (s : Finset (Index W Var Domain))

/-- Double negation elimination ([aloni-vanormondt-2023] Fact 1). -/
theorem support_neg_neg : support M (.neg (.neg φ)) s ↔ support M φ s :=
  Iff.rfl

/-- The De Morgan law `¬(φ ∨ ψ) ≡ ¬φ ∧ ¬ψ` ([aloni-vanormondt-2023] Fact 1). -/
theorem support_neg_disj :
    support M (.neg (.disj φ ψ)) s ↔ support M (.conj (.neg φ) (.neg ψ)) s :=
  Iff.rfl

/-- The De Morgan law `¬(φ ∧ ψ) ≡ ¬φ ∨ ¬ψ` ([aloni-vanormondt-2023] Fact 1). -/
theorem support_neg_conj :
    support M (.neg (.conj φ ψ)) s ↔ support M (.disj (.neg φ) (.neg ψ)) s :=
  Iff.rfl

/-- The modal duality `¬□φ ≡ ◇¬φ` ([aloni-vanormondt-2023] Fact 1). -/
theorem support_neg_nec :
    support M (.neg φ.nec) s ↔ support M (.poss (.neg φ)) s :=
  Iff.rfl

/-- The modal duality `¬◇φ ≡ □¬φ` ([aloni-vanormondt-2023] Fact 1). -/
theorem support_neg_poss :
    support M (.neg (.poss φ)) s ↔ support M (Formula.neg φ).nec s :=
  Iff.rfl

/-- The quantifier duality `¬∀xφ ≡ ∃x¬φ` ([aloni-vanormondt-2023] Fact 1). -/
theorem support_neg_univ :
    support M (.neg (.univ x φ)) s ↔ support M (.exi x (.neg φ)) s :=
  Iff.rfl

/-- The quantifier duality `¬∃xφ ≡ ∀x¬φ` ([aloni-vanormondt-2023] Fact 1). -/
theorem support_neg_exi :
    support M (.neg (.exi x φ)) s ↔ support M (.univ x (.neg φ)) s :=
  Iff.rfl

end Fact1

section Fragment

variable [DecidableEq W] [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain]

/-! ### Flatness as pointwise evaluation -/

theorem support_iff_forall_singleton {φ : Formula Var Const Pred}
    (hNE : φ.NEFree) (M : Model W Domain Const Pred)
    (s : Finset (Index W Var Domain)) :
    support M φ s ↔ ∀ i ∈ s, support M φ {i} :=
  isFlat_support_of_neFree hNE M s

theorem antiSupport_iff_forall_singleton {φ : Formula Var Const Pred}
    (hNE : φ.NEFree) (M : Model W Domain Const Pred)
    (s : Finset (Index W Var Domain)) :
    antiSupport M φ s ↔ ∀ i ∈ s, antiSupport M φ {i} :=
  support_iff_forall_singleton (.neg hNE) M s

/-! ### Atom substitution salva veritate -/

/-- Replacing each atom by a formula with the same support and anti-support preserves support
    and anti-support; [yan-2023]'s reinterpretation function (`Studies/Yan2023.lean`) uses this. -/
theorem eval_mapAtoms_iff (M : Model W Domain Const Pred)
    {fp : Pred → Var → Formula Var Const Pred}
    {fc : Pred → Const → Formula Var Const Pred}
    (hfp : ∀ (P : Pred) (x : Var) (b : Bool)
      (s : Finset (Index W Var Domain)),
      eval M b (fp P x) s ↔ eval M b (.pred P x) s)
    (hfc : ∀ (P : Pred) (c : Const) (b : Bool)
      (s : Finset (Index W Var Domain)),
      eval M b (fc P c) s ↔ eval M b (.predc P c) s)
    (φ : Formula Var Const Pred) :
    ∀ (b : Bool) (s : Finset (Index W Var Domain)),
      eval M b (φ.mapAtoms fp fc) s ↔ eval M b φ s := by
  induction φ with
  | pred P x => exact hfp P x
  | predc P c => exact hfc P c
  | _ => intro b s; cases b <;> simp only [Formula.mapAtoms, eval, *]

/-! ### Upward monotonicity of the NE-free fragment -/

theorem support_disj_inl (M : Model W Domain Const Pred)
    {α β : Formula Var Const Pred} (hβ : β.NEFree)
    {s : Finset (Index W Var Domain)} (h : support M α s) :
    support M (.disj α β) s :=
  ⟨s, h, ∅, support_empty_of_neFree hβ M, sup_bot_eq s⟩

@[simp] theorem support_nec_iff (M : Model W Domain Const Pred)
    (φ : Formula Var Const Pred) (s : Finset (Index W Var Domain)) :
    support M φ.nec s ↔
      ∀ i ∈ s, support M φ
        (State.modalLift (M.access i.world) i.assign) :=
  Iff.rfl

theorem support_nec_mono (M : Model W Domain Const Pred)
    {α β : Formula Var Const Pred}
    (h : ∀ t : Finset (Index W Var Domain), support M α t → support M β t)
    {s : Finset (Index W Var Domain)} (hα : support M α.nec s) :
    support M β.nec s :=
  fun i hi ↦ h _ (hα i hi)

end Fragment

/-! ### Classicality: the modal bridge

[aloni-vanormondt-2023] Proposition 4.1: `Formula.toModal` translates a formula into a
`ModalFormula` over the monadic signature (`Logic/Modal/FirstOrder/Semantics.lean`), and on
`NE`-free formulas support is Kripke satisfaction at every index. `NE` goes to `⊤`, as in BSML's
`Realize`, and each case of the proof is the law by which `flat` commutes with the clause's
operation. -/

open FirstOrder Language

/-- The translation of QBSML into first-order modal formulas over the monadic signature, which
sends `◇` to `ModalFormula.diamond`, the quantifiers to named binders and `NE` to `⊤`. -/
def Formula.toModal [DecidableEq Var] :
    Formula Var Const Pred → ModalFormula ((Language.monadic Pred)[[Const]]) Var
  | .pred P x => (predSymb P).modalFormula₁ (Term.var x)
  | .predc P c => (predSymb P).modalFormula₁ (((Language.monadic Pred).con c).term)
  | .ne => ⊤
  | .neg φ => φ.toModal.not
  | .conj φ ψ => φ.toModal ⊓ ψ.toModal
  | .disj φ ψ => φ.toModal ⊔ ψ.toModal
  | .poss φ => φ.toModal.diamond
  | .exi x φ => .ex x φ.toModal
  | .univ x φ => .all x φ.toModal

private lemma update_refines [DecidableEq Var] {i : Index W Var Domain} {v : Var → Domain}
    (hv : ∀ y, i.assign y = ↑(v y)) (x : Var) (d : Domain) :
    ∀ y, (i.update x d).assign y = ↑(Function.update v x d y) := by
  intro y
  rw [Index.assign_update]
  by_cases hy : y = x
  · subst hy
    rw [PartialAssign.update_self, Function.update_self]
  · rw [PartialAssign.update_of_ne hy, Function.update_of_ne hy]
    exact hv y

section Realize

variable [DecidableEq W] [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain]

private theorem setOf_eval_eq_flat {φ : Formula Var Const Pred} (hNE : φ.NEFree)
    (M : Model W Domain Const Pred) (b : Bool) :
    {t | eval M b φ t} = Team.flat fun j ↦ eval M b φ {j} := by
  ext t
  cases b
  · exact antiSupport_iff_forall_singleton hNE M t
  · exact support_iff_forall_singleton hNE M t

private theorem eval_singleton_iff_realize (M : Model W Domain Const Pred)
    {φ : Formula Var Const Pred} (hNE : φ.NEFree) (b : Bool) {i : Index W Var Domain}
    {v : Var → Domain} (hv : ∀ y, i.assign y = ↑(v y)) :
    eval M b φ {i} ↔ (φ.toModal.Realize M i.world v ↔ b) := by
  induction hNE generalizing b i v with
  | pred P x =>
    rw [Formula.toModal, ModalFormula.realize_rel₁, Term.realizeAt_var]
    cases b <;> simp [eval, hv]
  | predc P c =>
    rw [Formula.toModal, ModalFormula.realize_rel₁, ModalStructure.realizeAt_constants]
    cases b <;> simp [eval]
  | neg _ ih => cases b <;> simp [eval, Formula.toModal, ih _ hv]
  | conj h₁ h₂ ih₁ ih₂ =>
    cases b
    · simp only [eval]
      rw [setOf_eval_eq_flat h₁, setOf_eval_eq_flat h₂, Team.mem_tensor_flat]
      simp only [Finset.mem_singleton, forall_eq, ih₁ _ hv, ih₂ _ hv, Formula.toModal,
        ModalFormula.realize_inf, Bool.false_eq_true, iff_false]
      exact not_and_or.symm
    · simp [eval, ih₁ _ hv, ih₂ _ hv, Formula.toModal]
  | disj h₁ h₂ ih₁ ih₂ =>
    cases b
    · simp [eval, ih₁ _ hv, ih₂ _ hv, Formula.toModal, not_or]
    · simp only [eval]
      rw [setOf_eval_eq_flat h₁, setOf_eval_eq_flat h₂, Team.mem_tensor_flat]
      simp [ih₁ _ hv, ih₂ _ hv, Formula.toModal]
  | poss h ih =>
    have := fun b (w : W) ↦ ih b (i := (w, i.2)) hv
    simp only [Index.world] at this
    cases b
    · simp only [eval]
      rw [setOf_eval_eq_flat h, Team.nec_flat]
      simp [Index.world, Index.assign, this, Formula.toModal]
    · simp only [eval]
      rw [setOf_eval_eq_flat h, Team.poss_flat]
      simp [Index.world, Index.assign, this, Formula.toModal]
  | exi x h ih =>
    have := fun b d ↦ ih b (update_refines hv x d)
    cases b
    · simp only [eval]
      rw [setOf_eval_eq_flat h, Team.mem_necImage_flat]
      simp [this, Formula.toModal]
    · simp only [eval]
      rw [setOf_eval_eq_flat h, Team.mem_possLax_flat]
      simp [this, Formula.toModal]
  | univ x h ih =>
    have := fun b d ↦ ih b (update_refines hv x d)
    cases b
    · simp only [eval]
      rw [setOf_eval_eq_flat h, Team.mem_possLax_flat]
      simp [this, Formula.toModal]
    · simp only [eval]
      rw [setOf_eval_eq_flat h, Team.mem_necImage_flat]
      simp [this, Formula.toModal]

/-- A singleton state supports an `NE`-free formula iff its translation is satisfied at the
index's world ([aloni-vanormondt-2023] Proposition 4.1, singleton case). -/
theorem support_singleton_iff_realize (M : Model W Domain Const Pred)
    {φ : Formula Var Const Pred} (hNE : φ.NEFree) {i : Index W Var Domain} {v : Var → Domain}
    (hv : ∀ y, i.assign y = ↑(v y)) :
    support M φ {i} ↔ φ.toModal.Realize M i.world v := by
  simpa using eval_singleton_iff_realize M hNE true hv

theorem antiSupport_singleton_iff_realize (M : Model W Domain Const Pred)
    {φ : Formula Var Const Pred} (hNE : φ.NEFree) {i : Index W Var Domain} {v : Var → Domain}
    (hv : ∀ y, i.assign y = ↑(v y)) :
    antiSupport M φ {i} ↔ ¬ φ.toModal.Realize M i.world v := by
  simpa using eval_singleton_iff_realize M hNE false hv

/-- A state supports an `NE`-free formula iff its translation is satisfied at every index, that
is, `M, s ⊨ φ(x̄)` iff `M, w ⊨_g φ(x̄)` for all `⟨w, g⟩ ∈ s` ([aloni-vanormondt-2023] Proposition
4.1). -/
theorem support_iff_forall_realize (M : Model W Domain Const Pred) {φ : Formula Var Const Pred}
    (hNE : φ.NEFree) (s : Finset (Index W Var Domain)) (v : Index W Var Domain → Var → Domain)
    (hv : ∀ i ∈ s, ∀ y, i.assign y = ↑(v i y)) :
    support M φ s ↔ ∀ i ∈ s, φ.toModal.Realize M i.world (v i) := by
  rw [support_iff_forall_singleton hNE]
  exact forall₂_congr fun i hi ↦ support_singleton_iff_realize M hNE (hv i hi)

end Realize

end QBSML
