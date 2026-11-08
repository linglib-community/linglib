module

public import Linglib.Logic.Team.QBSML.Defs
public import Linglib.Logic.Team.Closure

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
* `den_mapAtoms`: replacing atoms by formulas with the same meaning preserves meaning.

## Implementation notes

Each closure property is proved for both coordinates of `Formula.den` by induction on the
formula, each case the lemma of its operation in `Team/Operations.lean`. The quantifier cases are
those of the box and the lax diamond of modal inclusion logic, both of which preserve union
closure; the strict diamond does not ([anttila-haggblom-yang-2025] p. 759).

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

/-- Support and anti-support are union closed. -/
theorem supClosed_den (M : Model W Domain Const Pred) (φ : Formula Var Const Pred) :
    SupClosed (φ.den M).pro ∧ SupClosed (φ.den M).con := by
  induction φ with
  | pred P x => exact ⟨supClosed_flat _, supClosed_flat _⟩
  | predc P c => exact ⟨supClosed_flat _, supClosed_flat _⟩
  | ne => exact ⟨supClosed_ne, supClosed_singleton_empty⟩
  | neg _ ih => exact ih.symm
  | conj _ _ ih₁ ih₂ => exact ⟨ih₁.1.inter ih₂.1, ih₁.2.sups ih₂.2⟩
  | disj _ _ ih₁ ih₂ => exact ⟨ih₁.1.sups ih₂.1, ih₁.2.inter ih₂.2⟩
  | poss _ _ => exact ⟨supClosed_flat _, supClosed_flat _⟩
  | exi x _ ih => exact ⟨ih.1.possLax, ih.2.necImage⟩
  | univ x _ ih => exact ⟨ih.1.necImage, ih.2.possLax⟩

/-- QBSML support is union closed, as BSML's is ([anttila-2021] Proposition 2.2.8).
[aloni-vanormondt-2023] Fact 2 states this for `NE`-free quantified formulas, but its argument
does not use the hypothesis. -/
theorem supClosed_support (M : Model W Domain Const Pred) (φ : Formula Var Const Pred) :
    SupClosed {s : Finset (Index W Var Domain) | support M φ s} :=
  (supClosed_den M φ).1

/-- The empty state supports and anti-supports every `NE`-free formula. -/
theorem empty_mem_den_of_neFree {φ : Formula Var Const Pred} (hNE : φ.NEFree)
    (M : Model W Domain Const Pred) : ∅ ∈ (φ.den M).pro ∧ ∅ ∈ (φ.den M).con := by
  induction hNE with
  | pred P x => exact ⟨empty_mem_flat _, empty_mem_flat _⟩
  | predc P c => exact ⟨empty_mem_flat _, empty_mem_flat _⟩
  | neg _ ih => exact ih.symm
  | conj _ _ ih₁ ih₂ => exact ⟨⟨ih₁.1, ih₂.1⟩, Set.bot_mem_sups ih₁.2 ih₂.2⟩
  | disj _ _ ih₁ ih₂ => exact ⟨Set.bot_mem_sups ih₁.1 ih₂.1, ⟨ih₁.2, ih₂.2⟩⟩
  | poss _ _ => exact ⟨empty_mem_flat _, empty_mem_flat _⟩
  | exi x _ ih => exact ⟨empty_mem_possLax ih.1, empty_mem_necImage ih.2⟩
  | univ x _ ih => exact ⟨empty_mem_necImage ih.1, empty_mem_possLax ih.2⟩

theorem support_empty_of_neFree {φ : Formula Var Const Pred}
    (hNE : φ.NEFree) (M : Model W Domain Const Pred) :
    support M φ ∅ :=
  (empty_mem_den_of_neFree hNE M).1

/-- Support and anti-support of an `NE`-free formula are downward closed. -/
theorem isLowerSet_den_of_neFree {φ : Formula Var Const Pred} (hNE : φ.NEFree)
    (M : Model W Domain Const Pred) : IsLowerSet (φ.den M).pro ∧ IsLowerSet (φ.den M).con := by
  induction hNE with
  | pred P x => exact ⟨isLowerSet_flat _, isLowerSet_flat _⟩
  | predc P c => exact ⟨isLowerSet_flat _, isLowerSet_flat _⟩
  | neg _ ih => exact ih.symm
  | conj _ _ ih₁ ih₂ => exact ⟨ih₁.1.inter ih₂.1, ih₁.2.sups ih₂.2⟩
  | disj _ _ ih₁ ih₂ => exact ⟨ih₁.1.sups ih₂.1, ih₁.2.inter ih₂.2⟩
  | poss _ _ => exact ⟨isLowerSet_flat _, isLowerSet_flat _⟩
  | exi x _ ih => exact ⟨ih.1.possLax, ih.2.necImage⟩
  | univ x _ ih => exact ⟨ih.1.necImage, ih.2.possLax⟩

/-- `NE`-free QBSML formulas are downward closed ([aloni-vanormondt-2023] Fact 2,
[anttila-2021] Proposition 2.2.8). -/
theorem isLowerSet_support_of_neFree {φ : Formula Var Const Pred}
    (hNE : φ.NEFree) (M : Model W Domain Const Pred) :
    IsLowerSet { t : Finset (Index W Var Domain) | support M φ t } :=
  (isLowerSet_den_of_neFree hNE M).1

/-! ### Flatness corollary -/

/-- NE-free QBSML formulas are flat, as BSML's are ([anttila-2021] Corollary 2.2.9). -/
theorem isFlat_support_of_neFree {φ : Formula Var Const Pred}
    (hNE : φ.NEFree) (M : Model W Domain Const Pred) :
    IsFlat { t : Finset (Index W Var Domain) | support M φ t } :=
  isFlat_of_isLowerSet_supClosed_empty
    (isLowerSet_support_of_neFree hNE M)
    (supClosed_support M φ)
    (support_empty_of_neFree hNE M)

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

/-- Replacing each atom by a formula with the same meaning preserves meaning; [yan-2023]'s
reinterpretation function (`Studies/Yan2023.lean`) uses this. -/
theorem den_mapAtoms (M : Model W Domain Const Pred) {fp : Pred → Var → Formula Var Const Pred}
    {fc : Pred → Const → Formula Var Const Pred}
    (hfp : ∀ P x, (fp P x).den M = (Formula.pred P x).den M)
    (hfc : ∀ P c, (fc P c).den M = (Formula.predc P c).den M) (φ : Formula Var Const Pred) :
    (φ.mapAtoms fp fc).den M = φ.den M := by
  induction φ with
  | pred P x => exact hfp P x
  | predc P c => exact hfc P c
  | _ => simp only [Formula.mapAtoms, Formula.den, *]

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

private theorem pro_den_eq_flat {φ : Formula Var Const Pred} (hNE : φ.NEFree)
    (M : Model W Domain Const Pred) : (φ.den M).pro = Team.flat fun j ↦ {j} ∈ (φ.den M).pro :=
  Set.ext (support_iff_forall_singleton hNE M)

private theorem con_den_eq_flat {φ : Formula Var Const Pred} (hNE : φ.NEFree)
    (M : Model W Domain Const Pred) : (φ.den M).con = Team.flat fun j ↦ {j} ∈ (φ.den M).con :=
  Set.ext (antiSupport_iff_forall_singleton hNE M)

private theorem singleton_mem_den_iff_realize (M : Model W Domain Const Pred)
    {φ : Formula Var Const Pred} (hNE : φ.NEFree) {i : Index W Var Domain}
    {v : Var → Domain} (hv : ∀ y, i.assign y = ↑(v y)) :
    ({i} ∈ (φ.den M).pro ↔ φ.toModal.Realize M i.world v) ∧
      ({i} ∈ (φ.den M).con ↔ ¬ φ.toModal.Realize M i.world v) := by
  induction hNE generalizing i v with
  | pred P x =>
    rw [Formula.toModal, ModalFormula.realize_rel₁, Term.realizeAt_var]
    constructor <;> simp [Formula.den, hv]
  | predc P c =>
    rw [Formula.toModal, ModalFormula.realize_rel₁, ModalStructure.realizeAt_constants]
    constructor <;> simp [Formula.den]
  | neg _ ih => simp [Formula.den, Formula.toModal, (ih hv).1, (ih hv).2]
  | conj h₁ h₂ ih₁ ih₂ =>
    refine ⟨by simp [Formula.den, (ih₁ hv).1, (ih₂ hv).1, Formula.toModal], ?_⟩
    simp only [Formula.den, Team.con_conj]
    rw [con_den_eq_flat h₁, con_den_eq_flat h₂, Team.mem_flat_sups_flat]
    simp only [Finset.mem_singleton, forall_eq, (ih₁ hv).2, (ih₂ hv).2, Formula.toModal,
      ModalFormula.realize_inf]
    exact not_and_or.symm
  | disj h₁ h₂ ih₁ ih₂ =>
    refine ⟨?_, by simp [Formula.den, (ih₁ hv).2, (ih₂ hv).2, Formula.toModal, not_or]⟩
    simp only [Formula.den, Team.pro_disj]
    rw [pro_den_eq_flat h₁, pro_den_eq_flat h₂, Team.mem_flat_sups_flat]
    simp [(ih₁ hv).1, (ih₂ hv).1, Formula.toModal]
  | poss h ih =>
    have h₁ := fun w : W ↦ (ih (i := (w, i.2)) hv).1
    have h₂ := fun w : W ↦ (ih (i := (w, i.2)) hv).2
    simp only [Index.world] at h₁ h₂
    constructor
    · simp only [Formula.den, Bilattice.Product.pro_map]
      rw [pro_den_eq_flat h, Team.poss_flat]
      simp [Index.world, Index.assign, h₁, Formula.toModal]
    · simp only [Formula.den, Bilattice.Product.con_map]
      rw [con_den_eq_flat h, Team.nec_flat]
      simp [Index.world, Index.assign, h₂, Formula.toModal]
  | exi x h ih =>
    have h₁ := fun d ↦ (ih (update_refines hv x d)).1
    have h₂ := fun d ↦ (ih (update_refines hv x d)).2
    constructor
    · simp only [Formula.den, Bilattice.Product.pro_map]
      rw [pro_den_eq_flat h, Team.mem_possLax_flat]
      simp [h₁, Formula.toModal]
    · simp only [Formula.den, Bilattice.Product.con_map]
      rw [con_den_eq_flat h, Team.mem_necImage_flat]
      simp [h₂, Formula.toModal]
  | univ x h ih =>
    have h₁ := fun d ↦ (ih (update_refines hv x d)).1
    have h₂ := fun d ↦ (ih (update_refines hv x d)).2
    constructor
    · simp only [Formula.den, Bilattice.Product.pro_map]
      rw [pro_den_eq_flat h, Team.mem_necImage_flat]
      simp [h₁, Formula.toModal]
    · simp only [Formula.den, Bilattice.Product.con_map]
      rw [con_den_eq_flat h, Team.mem_possLax_flat]
      simp [h₂, Formula.toModal]

/-- A singleton state supports an `NE`-free formula iff its translation is satisfied at the
index's world ([aloni-vanormondt-2023] Proposition 4.1, singleton case). -/
theorem support_singleton_iff_realize (M : Model W Domain Const Pred)
    {φ : Formula Var Const Pred} (hNE : φ.NEFree) {i : Index W Var Domain} {v : Var → Domain}
    (hv : ∀ y, i.assign y = ↑(v y)) :
    support M φ {i} ↔ φ.toModal.Realize M i.world v :=
  (singleton_mem_den_iff_realize M hNE hv).1

theorem antiSupport_singleton_iff_realize (M : Model W Domain Const Pred)
    {φ : Formula Var Const Pred} (hNE : φ.NEFree) {i : Index W Var Domain} {v : Var → Domain}
    (hv : ∀ y, i.assign y = ↑(v y)) :
    antiSupport M φ {i} ↔ ¬ φ.toModal.Realize M i.world v :=
  (singleton_mem_den_iff_realize M hNE hv).2

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
