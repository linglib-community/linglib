module

public import Mathlib.ModelTheory.Semantics
public import Linglib.Core.ModelTheory.Binders
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
* `Formula.toFormula?`, `support_iff_forall_realizeAt`: [aloni-vanormondt-2023] Proposition 4.1
  for modal-free formulas, with mathlib's `Formula.Realize` as classical satisfaction.
* `Formula.toModal?`, `support_iff_forall_realize`: Proposition 4.1 for all `NE`-free formulas.
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

/-- NE-free QBSML formulas are flat ([anttila-2021] Proposition 2.2.16). This follows from the
    three closure properties by [anttila-2021] Proposition 2.2.2 (`Team.isFlat_iff`). -/
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

/-! ### Classicality: the modal-free Realize bridge

[aloni-vanormondt-2023] Proposition 4.1 reduces the NE-free fragment to classical quantified modal
logic. This section proves the modal-free case against mathlib's first-order satisfaction.
`Formula.toFormula?` translates a formula into `((Language.monadic Pred)[[Const]]).Formula Var`,
with quantifiers as the named binders `Formula.all₁` / `Formula.ex₁` of
`Core/ModelTheory/Binders.lean`. Support at a singleton state is `Formula.Realize` in the structure
the model carries at that world (`support_singleton_iff_realizeAt`), and by flatness support at any
state is satisfaction at each of its indices (`support_iff_forall_realizeAt`). Modal formulas are
left to the next section, since mathlib's `ModelTheory` has no modal logic. -/

open FirstOrder Language

/-- The translation of a modal-free QBSML formula into a mathlib first-order formula over the
    monadic signature, with quantifiers as the named binders `Formula.all₁` / `Formula.ex₁`; it is
    `none` on `NE` and on modal formulas. -/
def Formula.toFormula? [DecidableEq Var] :
    Formula Var Const Pred → Option (((Language.monadic Pred)[[Const]]).Formula Var)
  | .pred P x => some ((predSymb P).formula₁ (Term.var x))
  | .predc P c => some ((predSymb P).formula₁ (((Language.monadic Pred).con c).term))
  | .neg φ => φ.toFormula?.map (·.not)
  | .conj φ ψ => φ.toFormula?.bind fun α ↦ ψ.toFormula?.map (α ⊓ ·)
  | .disj φ ψ => φ.toFormula?.bind fun α ↦ ψ.toFormula?.map (α ⊔ ·)
  | .exi x φ => φ.toFormula?.map (Formula.ex₁ x ·)
  | .univ x φ => φ.toFormula?.map (Formula.all₁ x ·)
  | _ => none

theorem neFree_of_toFormula? [DecidableEq Var] :
    ∀ {φ : Formula Var Const Pred} {ψ : ((Language.monadic Pred)[[Const]]).Formula Var},
      φ.toFormula? = some ψ → φ.NEFree := by
  intro φ
  induction φ with
  | pred P x => exact fun _ ↦ .pred P x
  | predc P c => exact fun _ ↦ .predc P c
  | neg φ ih =>
    intro ψ hψ
    cases hφ : φ.toFormula? with
    | none => simp [Formula.toFormula?, hφ] at hψ
    | some α => exact .neg (ih hφ)
  | conj φ₁ φ₂ ih₁ ih₂ =>
    intro ψ hψ
    cases hφ₁ : φ₁.toFormula? with
    | none => simp [Formula.toFormula?, hφ₁] at hψ
    | some α =>
      cases hφ₂ : φ₂.toFormula? with
      | none => simp [Formula.toFormula?, hφ₁, hφ₂] at hψ
      | some β => exact .conj (ih₁ hφ₁) (ih₂ hφ₂)
  | disj φ₁ φ₂ ih₁ ih₂ =>
    intro ψ hψ
    cases hφ₁ : φ₁.toFormula? with
    | none => simp [Formula.toFormula?, hφ₁] at hψ
    | some α =>
      cases hφ₂ : φ₂.toFormula? with
      | none => simp [Formula.toFormula?, hφ₁, hφ₂] at hψ
      | some β => exact .disj (ih₁ hφ₁) (ih₂ hφ₂)
  | exi x φ ih =>
    intro ψ hψ
    cases hφ : φ.toFormula? with
    | none => simp [Formula.toFormula?, hφ] at hψ
    | some α => exact .exi x (ih hφ)
  | univ x φ ih =>
    intro ψ hψ
    cases hφ : φ.toFormula? with
    | none => simp [Formula.toFormula?, hφ] at hψ
    | some α => exact .univ x (ih hφ)
  | ne => intro ψ hψ; simp [Formula.toFormula?] at hψ
  | poss _ _ => intro ψ hψ; simp [Formula.toFormula?] at hψ

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

section RealizeAt

variable [DecidableEq W] [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain]

private theorem support_and_antiSupport_singleton_realizeAt
    (M : Model W Domain Const Pred) :
    ∀ {φ : Formula Var Const Pred} {ψ : ((Language.monadic Pred)[[Const]]).Formula Var},
      φ.toFormula? = some ψ →
      ∀ {i : Index W Var Domain} {v : Var → Domain},
        (∀ y, i.assign y = ↑(v y)) →
        (support M φ {i} ↔ ψ.RealizeAt M.interp i.world v) ∧
        (antiSupport M φ {i} ↔ ¬ ψ.RealizeAt M.interp i.world v) := by
  intro φ
  induction φ with
  | pred P x =>
    intro ψ hψ i v hv
    rw [show (Formula.pred P x).toFormula? =
        some ((predSymb P).formula₁ (Term.var x)) from rfl,
      Option.some.injEq] at hψ
    subst hψ
    rw [ModalStructure.realizeAt_rel₁, Term.realizeAt_var]
    constructor
    · constructor
      · intro h
        obtain ⟨d, hd, hP⟩ := h i (Finset.mem_singleton_self i)
        rw [hv x, Flat.coe_inj] at hd
        rw [hd]
        exact hP
      · intro h j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        exact ⟨v x, hv x, h⟩
    · constructor
      · intro h hP
        obtain ⟨d, hd, hnP⟩ := h i (Finset.mem_singleton_self i)
        rw [hv x, Flat.coe_inj] at hd
        exact hnP (hd ▸ hP)
      · intro h j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        exact ⟨v x, hv x, h⟩
  | predc P c =>
    intro ψ hψ i v hv
    rw [show (Formula.predc P c).toFormula? =
        some ((predSymb P).formula₁ (((Language.monadic Pred).con c).term))
        from rfl,
      Option.some.injEq] at hψ
    subst hψ
    rw [ModalStructure.realizeAt_rel₁, ModalStructure.realizeAt_constants]
    constructor
    · constructor
      · intro h
        exact h i (Finset.mem_singleton_self i)
      · intro h j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        exact h
    · constructor
      · intro h
        exact h i (Finset.mem_singleton_self i)
      · intro h j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        exact h
  | neg φ ih =>
    intro ψ hψ i v hv
    cases hφ : φ.toFormula? with
    | none => simp [Formula.toFormula?, hφ] at hψ
    | some α =>
      simp only [Formula.toFormula?, hφ] at hψ
      rw [Option.map_some, Option.some.injEq] at hψ
      subst hψ
      obtain ⟨ihs, iha⟩ := ih hφ hv
      constructor
      · rw [Formula.realizeAt_not]
        exact iha
      · rw [Formula.realizeAt_not, not_not]
        exact ihs
  | conj φ₁ φ₂ ih₁ ih₂ =>
    intro ψ hψ i v hv
    cases hφ₁ : φ₁.toFormula? with
    | none => simp [Formula.toFormula?, hφ₁] at hψ
    | some α =>
      cases hφ₂ : φ₂.toFormula? with
      | none => simp [Formula.toFormula?, hφ₁, hφ₂] at hψ
      | some β =>
        simp only [Formula.toFormula?, hφ₁, hφ₂] at hψ
        rw [Option.bind_some, Option.map_some, Option.some.injEq] at hψ
        subst hψ
        obtain ⟨ih₁s, ih₁a⟩ := ih₁ hφ₁ hv
        obtain ⟨ih₂s, ih₂a⟩ := ih₂ hφ₂ hv
        constructor
        · rw [Formula.realizeAt_inf]
          exact and_congr ih₁s ih₂s
        · rw [Formula.realizeAt_inf, not_and_or]
          constructor
          · rintro ⟨t₁, h₁, t₂, h₂, hsplit⟩
            have hsub₁ : t₁ ⊆ ({i} : Finset (Index W Var Domain)) :=
              le_sup_left.trans_eq hsplit
            rcases Finset.subset_singleton_iff.mp hsub₁ with ht₁ | ht₁
            · have ht₂ : t₂ = {i} := by
                subst ht₁
                have h' : (∅ ∪ t₂ : Finset (Index W Var Domain)) = {i} := hsplit
                simpa using h'
              exact Or.inr (ih₂a.mp (ht₂ ▸ h₂))
            · exact Or.inl (ih₁a.mp (ht₁ ▸ h₁))
          · rintro (h | h)
            · exact ⟨{i}, ih₁a.mpr h, ∅, (support_and_antiSupport_empty_of_neFree
                  (neFree_of_toFormula? hφ₂) M).2, sup_bot_eq _⟩
            · exact ⟨∅, (support_and_antiSupport_empty_of_neFree
                  (neFree_of_toFormula? hφ₁) M).2, {i}, ih₂a.mpr h, bot_sup_eq _⟩
  | disj φ₁ φ₂ ih₁ ih₂ =>
    intro ψ hψ i v hv
    cases hφ₁ : φ₁.toFormula? with
    | none => simp [Formula.toFormula?, hφ₁] at hψ
    | some α =>
      cases hφ₂ : φ₂.toFormula? with
      | none => simp [Formula.toFormula?, hφ₁, hφ₂] at hψ
      | some β =>
        simp only [Formula.toFormula?, hφ₁, hφ₂] at hψ
        rw [Option.bind_some, Option.map_some, Option.some.injEq] at hψ
        subst hψ
        obtain ⟨ih₁s, ih₁a⟩ := ih₁ hφ₁ hv
        obtain ⟨ih₂s, ih₂a⟩ := ih₂ hφ₂ hv
        constructor
        · rw [Formula.realizeAt_sup]
          constructor
          · rintro ⟨t₁, h₁, t₂, h₂, hsplit⟩
            have hsub₁ : t₁ ⊆ ({i} : Finset (Index W Var Domain)) :=
              le_sup_left.trans_eq hsplit
            rcases Finset.subset_singleton_iff.mp hsub₁ with ht₁ | ht₁
            · have ht₂ : t₂ = {i} := by
                subst ht₁
                have h' : (∅ ∪ t₂ : Finset (Index W Var Domain)) = {i} := hsplit
                simpa using h'
              exact Or.inr (ih₂s.mp (ht₂ ▸ h₂))
            · exact Or.inl (ih₁s.mp (ht₁ ▸ h₁))
          · rintro (h | h)
            · exact ⟨{i}, ih₁s.mpr h, ∅, (support_and_antiSupport_empty_of_neFree
                  (neFree_of_toFormula? hφ₂) M).1, sup_bot_eq _⟩
            · exact ⟨∅, (support_and_antiSupport_empty_of_neFree
                  (neFree_of_toFormula? hφ₁) M).1, {i}, ih₂s.mpr h, bot_sup_eq _⟩
        · rw [Formula.realizeAt_sup, not_or]
          exact and_congr ih₁a ih₂a
  | exi x φ ih =>
    intro ψ hψ i v hv
    cases hφ : φ.toFormula? with
    | none => simp [Formula.toFormula?, hφ] at hψ
    | some α =>
      simp only [Formula.toFormula?, hφ] at hψ
      rw [Option.map_some, Option.some.injEq] at hψ
      subst hψ
      have hNE : φ.NEFree := neFree_of_toFormula? hφ
      constructor
      · rw [support_exi_iff, Formula.realizeAt_ex₁]
        constructor
        · rintro ⟨h, hne, hsupp⟩
          have hsupp' := (support_iff_forall_singleton hNE M _).mp hsupp
          obtain ⟨d, hd⟩ := hne i (Finset.mem_singleton_self i)
          exact ⟨d, ((ih hφ (update_refines hv x d)).1).mp
            (hsupp' (i.update x d) (State.mem_extendFunctional.mpr
              ⟨i, Finset.mem_singleton_self i, d, hd, rfl⟩))⟩
        · rintro ⟨d, hd⟩
          refine ⟨fun _ ↦ {d}, fun j _ ↦ Finset.singleton_nonempty d,
            (support_iff_forall_singleton hNE M _).mpr ?_⟩
          intro j hj
          obtain ⟨i', hi', d', hd', hupd⟩ := State.mem_extendFunctional.mp hj
          rw [Finset.mem_singleton] at hi' hd'
          subst hi'
          subst hd'
          subst hupd
          exact ((ih hφ (update_refines hv x d')).1).mpr hd
      · rw [Formula.realizeAt_ex₁, not_exists]
        show antiSupport M φ (State.extendUniversal {i} x) ↔ _
        rw [antiSupport_iff_forall_singleton hNE]
        constructor
        · intro h d
          exact ((ih hφ (update_refines hv x d)).2).mp
            (h (i.update x d) (State.mem_extendUniversal.mpr
              ⟨i, Finset.mem_singleton_self i, d, rfl⟩))
        · intro h j hj
          obtain ⟨i', hi', d, hupd⟩ := State.mem_extendUniversal.mp hj
          rw [Finset.mem_singleton] at hi'
          subst hi'
          subst hupd
          exact ((ih hφ (update_refines hv x d)).2).mpr (h d)
  | univ x φ ih =>
    intro ψ hψ i v hv
    cases hφ : φ.toFormula? with
    | none => simp [Formula.toFormula?, hφ] at hψ
    | some α =>
      simp only [Formula.toFormula?, hφ] at hψ
      rw [Option.map_some, Option.some.injEq] at hψ
      subst hψ
      have hNE : φ.NEFree := neFree_of_toFormula? hφ
      constructor
      · rw [Formula.realizeAt_all₁]
        show support M φ (State.extendUniversal {i} x) ↔ _
        rw [support_iff_forall_singleton hNE]
        constructor
        · intro h d
          exact ((ih hφ (update_refines hv x d)).1).mp
            (h (i.update x d) (State.mem_extendUniversal.mpr
              ⟨i, Finset.mem_singleton_self i, d, rfl⟩))
        · intro h j hj
          obtain ⟨i', hi', d, hupd⟩ := State.mem_extendUniversal.mp hj
          rw [Finset.mem_singleton] at hi'
          subst hi'
          subst hupd
          exact ((ih hφ (update_refines hv x d)).1).mpr (h d)
      · rw [antiSupport_univ_iff, Formula.realizeAt_all₁, not_forall]
        constructor
        · rintro ⟨h, hne, hanti⟩
          have hanti' := (antiSupport_iff_forall_singleton hNE M _).mp hanti
          obtain ⟨d, hd⟩ := hne i (Finset.mem_singleton_self i)
          exact ⟨d, ((ih hφ (update_refines hv x d)).2).mp
            (hanti' (i.update x d) (State.mem_extendFunctional.mpr
              ⟨i, Finset.mem_singleton_self i, d, hd, rfl⟩))⟩
        · rintro ⟨d, hd⟩
          refine ⟨fun _ ↦ {d}, fun j _ ↦ Finset.singleton_nonempty d,
            (antiSupport_iff_forall_singleton hNE M _).mpr ?_⟩
          intro j hj
          obtain ⟨i', hi', d', hd', hupd⟩ := State.mem_extendFunctional.mp hj
          rw [Finset.mem_singleton] at hi' hd'
          subst hi'
          subst hd'
          subst hupd
          exact ((ih hφ (update_refines hv x d')).2).mpr hd
  | ne => intro ψ hψ; simp [Formula.toFormula?] at hψ
  | poss _ _ => intro ψ hψ; simp [Formula.toFormula?] at hψ

/-- A singleton state supports a translatable modal-free formula iff the translation is satisfied
    at the index's world, under any total valuation extending the index's partial assignment
    ([aloni-vanormondt-2023] Proposition 4.1, singleton case). -/
theorem support_singleton_iff_realizeAt (M : Model W Domain Const Pred)
    {φ : Formula Var Const Pred} {ψ : ((Language.monadic Pred)[[Const]]).Formula Var}
    (hψ : φ.toFormula? = some ψ) {i : Index W Var Domain}
    {v : Var → Domain} (hv : ∀ y, i.assign y = ↑(v y)) :
    support M φ {i} ↔ ψ.RealizeAt M.interp i.world v :=
  (support_and_antiSupport_singleton_realizeAt M hψ hv).1

theorem antiSupport_singleton_iff_realizeAt (M : Model W Domain Const Pred)
    {φ : Formula Var Const Pred} {ψ : ((Language.monadic Pred)[[Const]]).Formula Var}
    (hψ : φ.toFormula? = some ψ) {i : Index W Var Domain}
    {v : Var → Domain} (hv : ∀ y, i.assign y = ↑(v y)) :
    antiSupport M φ {i} ↔ ¬ ψ.RealizeAt M.interp i.world v :=
  (support_and_antiSupport_singleton_realizeAt M hψ hv).2

/-- A state supports a translatable modal-free formula iff the translation is satisfied at every
index, that is, `M, s ⊨ φ(x̄)` iff `M, w ⊨_g φ(x̄)` for all `⟨w, g⟩ ∈ s` ([aloni-vanormondt-2023]
Proposition 4.1, modal-free case). -/
theorem support_iff_forall_realizeAt (M : Model W Domain Const Pred)
    {φ : Formula Var Const Pred} {ψ : ((Language.monadic Pred)[[Const]]).Formula Var}
    (hψ : φ.toFormula? = some ψ) (s : Finset (Index W Var Domain))
    (v : Index W Var Domain → Var → Domain)
    (hv : ∀ i ∈ s, ∀ y, i.assign y = ↑(v i y)) :
    support M φ s ↔ ∀ i ∈ s, ψ.RealizeAt M.interp i.world (v i) := by
  rw [support_iff_forall_singleton (neFree_of_toFormula? hψ)]
  exact forall₂_congr fun i hi ↦
    support_singleton_iff_realizeAt M hψ (hv i hi)

end RealizeAt

/-! ### Classicality II: the full modal bridge

[aloni-vanormondt-2023] Proposition 4.1 in full: `Formula.toModal?` translates every NE-free
formula, modal or not, into a `ModalFormula` over the monadic signature
(`Logic/Modal/FirstOrder/Semantics.lean`), and support is Kripke satisfaction at every index. The
translation is defined exactly on the NE-free formulas. -/

/-- The translation of QBSML into first-order modal formulas over the monadic signature, which sends
`◇` to `ModalFormula.diamond` and quantifiers to named binders. Only `NE` has no translation. -/
def Formula.toModal? [DecidableEq Var] :
    Formula Var Const Pred →
      Option (ModalFormula ((Language.monadic Pred)[[Const]]) Var)
  | .pred P x => some ((predSymb P).modalFormula₁ (Term.var x))
  | .predc P c =>
      some ((predSymb P).modalFormula₁ (((Language.monadic Pred).con c).term))
  | .ne => none
  | .neg φ => φ.toModal?.map .not
  | .conj φ ψ =>
      φ.toModal?.bind fun α ↦ ψ.toModal?.map (α ⊓ ·)
  | .disj φ ψ =>
      φ.toModal?.bind fun α ↦ ψ.toModal?.map (α ⊔ ·)
  | .poss φ => φ.toModal?.map ModalFormula.diamond
  | .exi x φ => φ.toModal?.map (ModalFormula.ex x ·)
  | .univ x φ => φ.toModal?.map (ModalFormula.all x ·)

theorem neFree_of_toModal? [DecidableEq Var] :
    ∀ {φ : Formula Var Const Pred}
      {τ : ModalFormula ((Language.monadic Pred)[[Const]]) Var},
      φ.toModal? = some τ → φ.NEFree := by
  intro φ
  induction φ with
  | pred P x => exact fun _ ↦ .pred P x
  | predc P c => exact fun _ ↦ .predc P c
  | neg φ ih =>
    intro τ hτ
    cases hφ : φ.toModal? with
    | none => simp [Formula.toModal?, hφ] at hτ
    | some α => exact .neg (ih hφ)
  | conj φ₁ φ₂ ih₁ ih₂ =>
    intro τ hτ
    cases hφ₁ : φ₁.toModal? with
    | none => simp [Formula.toModal?, hφ₁] at hτ
    | some α =>
      cases hφ₂ : φ₂.toModal? with
      | none => simp [Formula.toModal?, hφ₁, hφ₂] at hτ
      | some β => exact .conj (ih₁ hφ₁) (ih₂ hφ₂)
  | disj φ₁ φ₂ ih₁ ih₂ =>
    intro τ hτ
    cases hφ₁ : φ₁.toModal? with
    | none => simp [Formula.toModal?, hφ₁] at hτ
    | some α =>
      cases hφ₂ : φ₂.toModal? with
      | none => simp [Formula.toModal?, hφ₁, hφ₂] at hτ
      | some β => exact .disj (ih₁ hφ₁) (ih₂ hφ₂)
  | poss φ ih =>
    intro τ hτ
    cases hφ : φ.toModal? with
    | none => simp [Formula.toModal?, hφ] at hτ
    | some α => exact .poss (ih hφ)
  | exi x φ ih =>
    intro τ hτ
    cases hφ : φ.toModal? with
    | none => simp [Formula.toModal?, hφ] at hτ
    | some α => exact .exi x (ih hφ)
  | univ x φ ih =>
    intro τ hτ
    cases hφ : φ.toModal? with
    | none => simp [Formula.toModal?, hφ] at hτ
    | some α => exact .univ x (ih hφ)
  | ne => intro τ hτ; simp [Formula.toModal?] at hτ

theorem exists_toModal?_of_neFree [DecidableEq Var] :
    ∀ {φ : Formula Var Const Pred}, φ.NEFree →
      ∃ τ, φ.toModal? = some τ := by
  intro φ h
  induction h with
  | pred P x => exact ⟨_, rfl⟩
  | predc P c => exact ⟨_, rfl⟩
  | neg _ ih =>
    obtain ⟨τ, hτ⟩ := ih
    exact ⟨.not τ, by simp [Formula.toModal?, hτ]⟩
  | conj _ _ ih₁ ih₂ =>
    obtain ⟨τ₁, hτ₁⟩ := ih₁
    obtain ⟨τ₂, hτ₂⟩ := ih₂
    exact ⟨τ₁ ⊓ τ₂, by simp [Formula.toModal?, hτ₁, hτ₂]⟩
  | disj _ _ ih₁ ih₂ =>
    obtain ⟨τ₁, hτ₁⟩ := ih₁
    obtain ⟨τ₂, hτ₂⟩ := ih₂
    exact ⟨τ₁ ⊔ τ₂, by simp [Formula.toModal?, hτ₁, hτ₂]⟩
  | poss _ ih =>
    obtain ⟨τ, hτ⟩ := ih
    exact ⟨τ.diamond, by simp [Formula.toModal?, hτ]⟩
  | @exi x _ _ ih =>
    obtain ⟨τ, hτ⟩ := ih
    exact ⟨.ex x τ, by simp [Formula.toModal?, hτ]⟩
  | @univ x _ _ ih =>
    obtain ⟨τ, hτ⟩ := ih
    exact ⟨.all x τ, by simp [Formula.toModal?, hτ]⟩

section Realize

variable [DecidableEq W] [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain]

private theorem support_and_antiSupport_singleton_realize
    (M : Model W Domain Const Pred) :
    ∀ {φ : Formula Var Const Pred}
      {τ : ModalFormula ((Language.monadic Pred)[[Const]]) Var},
      φ.toModal? = some τ →
      ∀ {i : Index W Var Domain} {v : Var → Domain},
        (∀ y, i.assign y = ↑(v y)) →
        (support M φ {i} ↔ τ.Realize M i.world v) ∧
        (antiSupport M φ {i} ↔ ¬ τ.Realize M i.world v) := by
  intro φ
  induction φ with
  | pred P x =>
    intro τ hτ i v hv
    rw [show (Formula.pred P x).toModal? =
        some ((predSymb P).modalFormula₁ (Term.var x)) from rfl,
      Option.some.injEq] at hτ
    subst hτ
    rw [ModalFormula.realize_rel₁, Term.realizeAt_var]
    constructor
    · constructor
      · intro h
        obtain ⟨d, hd, hP⟩ := h i (Finset.mem_singleton_self i)
        rw [hv x, Flat.coe_inj] at hd
        rw [hd]
        exact hP
      · intro h j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        exact ⟨v x, hv x, h⟩
    · constructor
      · intro h hP
        obtain ⟨d, hd, hnP⟩ := h i (Finset.mem_singleton_self i)
        rw [hv x, Flat.coe_inj] at hd
        exact hnP (hd ▸ hP)
      · intro h j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        exact ⟨v x, hv x, h⟩
  | predc P c =>
    intro τ hτ i v hv
    rw [show (Formula.predc P c).toModal? =
        some ((predSymb P).modalFormula₁
          (((Language.monadic Pred).con c).term)) from rfl,
      Option.some.injEq] at hτ
    subst hτ
    rw [ModalFormula.realize_rel₁, ModalStructure.realizeAt_constants]
    constructor
    · constructor
      · intro h
        exact h i (Finset.mem_singleton_self i)
      · intro h j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        exact h
    · constructor
      · intro h
        exact h i (Finset.mem_singleton_self i)
      · intro h j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        exact h
  | neg φ ih =>
    intro τ hτ i v hv
    cases hφ : φ.toModal? with
    | none => simp [Formula.toModal?, hφ] at hτ
    | some α =>
      simp only [Formula.toModal?, hφ] at hτ
      rw [Option.map_some, Option.some.injEq] at hτ
      subst hτ
      obtain ⟨ihs, iha⟩ := ih hφ hv
      constructor
      · rw [ModalFormula.realize_not]
        exact iha
      · rw [ModalFormula.realize_not, not_not]
        exact ihs
  | conj φ₁ φ₂ ih₁ ih₂ =>
    intro τ hτ i v hv
    cases hφ₁ : φ₁.toModal? with
    | none => simp [Formula.toModal?, hφ₁] at hτ
    | some α =>
      cases hφ₂ : φ₂.toModal? with
      | none => simp [Formula.toModal?, hφ₁, hφ₂] at hτ
      | some β =>
        simp only [Formula.toModal?, hφ₁, hφ₂] at hτ
        rw [Option.bind_some, Option.map_some, Option.some.injEq] at hτ
        subst hτ
        obtain ⟨ih₁s, ih₁a⟩ := ih₁ hφ₁ hv
        obtain ⟨ih₂s, ih₂a⟩ := ih₂ hφ₂ hv
        constructor
        · rw [ModalFormula.realize_inf]
          exact and_congr ih₁s ih₂s
        · rw [ModalFormula.realize_inf, not_and_or]
          constructor
          · rintro ⟨t₁, h₁, t₂, h₂, hsplit⟩
            have hsub₁ : t₁ ⊆ ({i} : Finset (Index W Var Domain)) :=
              le_sup_left.trans_eq hsplit
            rcases Finset.subset_singleton_iff.mp hsub₁ with ht₁ | ht₁
            · have ht₂ : t₂ = {i} := by
                subst ht₁
                have h' : (∅ ∪ t₂ : Finset (Index W Var Domain)) = {i} :=
                  hsplit
                simpa using h'
              exact Or.inr (ih₂a.mp (ht₂ ▸ h₂))
            · exact Or.inl (ih₁a.mp (ht₁ ▸ h₁))
          · rintro (h | h)
            · exact ⟨{i}, ih₁a.mpr h, ∅, (support_and_antiSupport_empty_of_neFree
                  (neFree_of_toModal? hφ₂) M).2, sup_bot_eq _⟩
            · exact ⟨∅, (support_and_antiSupport_empty_of_neFree
                  (neFree_of_toModal? hφ₁) M).2, {i}, ih₂a.mpr h, bot_sup_eq _⟩
  | disj φ₁ φ₂ ih₁ ih₂ =>
    intro τ hτ i v hv
    cases hφ₁ : φ₁.toModal? with
    | none => simp [Formula.toModal?, hφ₁] at hτ
    | some α =>
      cases hφ₂ : φ₂.toModal? with
      | none => simp [Formula.toModal?, hφ₁, hφ₂] at hτ
      | some β =>
        simp only [Formula.toModal?, hφ₁, hφ₂] at hτ
        rw [Option.bind_some, Option.map_some, Option.some.injEq] at hτ
        subst hτ
        obtain ⟨ih₁s, ih₁a⟩ := ih₁ hφ₁ hv
        obtain ⟨ih₂s, ih₂a⟩ := ih₂ hφ₂ hv
        constructor
        · rw [ModalFormula.realize_sup]
          constructor
          · rintro ⟨t₁, h₁, t₂, h₂, hsplit⟩
            have hsub₁ : t₁ ⊆ ({i} : Finset (Index W Var Domain)) :=
              le_sup_left.trans_eq hsplit
            rcases Finset.subset_singleton_iff.mp hsub₁ with ht₁ | ht₁
            · have ht₂ : t₂ = {i} := by
                subst ht₁
                have h' : (∅ ∪ t₂ : Finset (Index W Var Domain)) = {i} :=
                  hsplit
                simpa using h'
              exact Or.inr (ih₂s.mp (ht₂ ▸ h₂))
            · exact Or.inl (ih₁s.mp (ht₁ ▸ h₁))
          · rintro (h | h)
            · exact ⟨{i}, ih₁s.mpr h, ∅, (support_and_antiSupport_empty_of_neFree
                  (neFree_of_toModal? hφ₂) M).1, sup_bot_eq _⟩
            · exact ⟨∅, (support_and_antiSupport_empty_of_neFree
                  (neFree_of_toModal? hφ₁) M).1, {i}, ih₂s.mpr h, bot_sup_eq _⟩
        · rw [ModalFormula.realize_sup, not_or]
          exact and_congr ih₁a ih₂a
  | poss φ ih =>
    intro τ hτ i v hv
    cases hφ : φ.toModal? with
    | none => simp [Formula.toModal?, hφ] at hτ
    | some α =>
      simp only [Formula.toModal?, hφ] at hτ
      rw [Option.map_some, Option.some.injEq] at hτ
      subst hτ
      have hNE : φ.NEFree := neFree_of_toModal? hφ
      constructor
      · rw [support_poss_iff, ModalFormula.realize_diamond]
        constructor
        · intro h
          obtain ⟨X, hX, ⟨w', hw'⟩, hsupp⟩ :=
            h i (Finset.mem_singleton_self i)
          have hs := (support_iff_forall_singleton hNE M _).mp hsupp
            (w', i.assign) (State.mem_modalLift.mpr ⟨hw', rfl⟩)
          exact ⟨w', hX hw', ((ih hφ (i := (w', i.assign)) hv).1).mp hs⟩
        · rintro ⟨w', hw', hreal⟩ j hj
          rw [Finset.mem_singleton] at hj
          subst hj
          refine ⟨{w'}, Finset.singleton_subset_iff.mpr hw',
            Finset.singleton_nonempty _, ?_⟩
          rw [State.modalLift_singleton]
          exact ((ih hφ (i := (w', j.assign)) hv).1).mpr hreal
      · constructor
        · intro h hex
          rw [ModalFormula.realize_diamond] at hex
          obtain ⟨w', hw', hreal⟩ := hex
          have hanti := (antiSupport_iff_forall_singleton hNE M _).mp
            (h i (Finset.mem_singleton_self i)) (w', i.assign)
            (State.mem_modalLift.mpr ⟨hw', rfl⟩)
          exact ((ih hφ (i := (w', i.assign)) hv).2).mp hanti hreal
        · intro h j hj
          rw [Finset.mem_singleton] at hj
          subst hj
          refine (antiSupport_iff_forall_singleton hNE M _).mpr ?_
          intro k hk
          obtain ⟨hkw, hka⟩ := State.mem_modalLift.mp hk
          refine ((ih hφ (i := k) fun y ↦ by rw [hka]; exact hv y).2).mpr ?_
          intro hreal
          exact h ((ModalFormula.realize_diamond M j.world v α).mpr
            ⟨k.world, hkw, hreal⟩)
  | exi x φ ih =>
    intro τ hτ i v hv
    cases hφ : φ.toModal? with
    | none => simp [Formula.toModal?, hφ] at hτ
    | some α =>
      simp only [Formula.toModal?, hφ] at hτ
      rw [Option.map_some, Option.some.injEq] at hτ
      subst hτ
      have hNE : φ.NEFree := neFree_of_toModal? hφ
      constructor
      · rw [support_exi_iff, ModalFormula.realize_ex]
        constructor
        · rintro ⟨h, hne, hsupp⟩
          have hsupp' := (support_iff_forall_singleton hNE M _).mp hsupp
          obtain ⟨d, hd⟩ := hne i (Finset.mem_singleton_self i)
          exact ⟨d, ((ih hφ (update_refines hv x d)).1).mp
            (hsupp' (i.update x d) (State.mem_extendFunctional.mpr
              ⟨i, Finset.mem_singleton_self i, d, hd, rfl⟩))⟩
        · rintro ⟨d, hd⟩
          refine ⟨fun _ ↦ {d}, fun j _ ↦ Finset.singleton_nonempty d,
            (support_iff_forall_singleton hNE M _).mpr ?_⟩
          intro j hj
          obtain ⟨i', hi', d', hd', hupd⟩ := State.mem_extendFunctional.mp hj
          rw [Finset.mem_singleton] at hi' hd'
          subst hi'
          subst hd'
          subst hupd
          exact ((ih hφ (update_refines hv x d')).1).mpr hd
      · rw [ModalFormula.realize_ex, not_exists]
        show antiSupport M φ (State.extendUniversal {i} x) ↔ _
        rw [antiSupport_iff_forall_singleton hNE]
        constructor
        · intro h d
          exact ((ih hφ (update_refines hv x d)).2).mp
            (h (i.update x d) (State.mem_extendUniversal.mpr
              ⟨i, Finset.mem_singleton_self i, d, rfl⟩))
        · intro h j hj
          obtain ⟨i', hi', d, hupd⟩ := State.mem_extendUniversal.mp hj
          rw [Finset.mem_singleton] at hi'
          subst hi'
          subst hupd
          exact ((ih hφ (update_refines hv x d)).2).mpr (h d)
  | univ x φ ih =>
    intro τ hτ i v hv
    cases hφ : φ.toModal? with
    | none => simp [Formula.toModal?, hφ] at hτ
    | some α =>
      simp only [Formula.toModal?, hφ] at hτ
      rw [Option.map_some, Option.some.injEq] at hτ
      subst hτ
      have hNE : φ.NEFree := neFree_of_toModal? hφ
      constructor
      · rw [ModalFormula.realize_all]
        show support M φ (State.extendUniversal {i} x) ↔ _
        rw [support_iff_forall_singleton hNE]
        constructor
        · intro h d
          exact ((ih hφ (update_refines hv x d)).1).mp
            (h (i.update x d) (State.mem_extendUniversal.mpr
              ⟨i, Finset.mem_singleton_self i, d, rfl⟩))
        · intro h j hj
          obtain ⟨i', hi', d, hupd⟩ := State.mem_extendUniversal.mp hj
          rw [Finset.mem_singleton] at hi'
          subst hi'
          subst hupd
          exact ((ih hφ (update_refines hv x d)).1).mpr (h d)
      · rw [antiSupport_univ_iff, ModalFormula.realize_all, not_forall]
        constructor
        · rintro ⟨h, hne, hanti⟩
          have hanti' := (antiSupport_iff_forall_singleton hNE M _).mp hanti
          obtain ⟨d, hd⟩ := hne i (Finset.mem_singleton_self i)
          exact ⟨d, ((ih hφ (update_refines hv x d)).2).mp
            (hanti' (i.update x d) (State.mem_extendFunctional.mpr
              ⟨i, Finset.mem_singleton_self i, d, hd, rfl⟩))⟩
        · rintro ⟨d, hd⟩
          refine ⟨fun _ ↦ {d}, fun j _ ↦ Finset.singleton_nonempty d,
            (antiSupport_iff_forall_singleton hNE M _).mpr ?_⟩
          intro j hj
          obtain ⟨i', hi', d', hd', hupd⟩ := State.mem_extendFunctional.mp hj
          rw [Finset.mem_singleton] at hi' hd'
          subst hi'
          subst hd'
          subst hupd
          exact ((ih hφ (update_refines hv x d')).2).mpr hd
  | ne => intro τ hτ; simp [Formula.toModal?] at hτ

/-- A singleton state supports a modally translatable formula iff its translation is satisfied
    at the index's world ([aloni-vanormondt-2023] Proposition 4.1, singleton case). -/
theorem support_singleton_iff_realize (M : Model W Domain Const Pred)
    {φ : Formula Var Const Pred}
    {τ : ModalFormula ((Language.monadic Pred)[[Const]]) Var}
    (hτ : φ.toModal? = some τ) {i : Index W Var Domain}
    {v : Var → Domain} (hv : ∀ y, i.assign y = ↑(v y)) :
    support M φ {i} ↔ τ.Realize M i.world v :=
  (support_and_antiSupport_singleton_realize M hτ hv).1

theorem antiSupport_singleton_iff_realize (M : Model W Domain Const Pred)
    {φ : Formula Var Const Pred}
    {τ : ModalFormula ((Language.monadic Pred)[[Const]]) Var}
    (hτ : φ.toModal? = some τ) {i : Index W Var Domain}
    {v : Var → Domain} (hv : ∀ y, i.assign y = ↑(v y)) :
    antiSupport M φ {i} ↔ ¬ τ.Realize M i.world v :=
  (support_and_antiSupport_singleton_realize M hτ hv).2

/-- A state supports an NE-free formula iff its modal translation is satisfied at every index, that
is, `M, s ⊨ φ(x̄)` iff `M, w ⊨_g φ(x̄)` for all `⟨w, g⟩ ∈ s` ([aloni-vanormondt-2023] Proposition
4.1). -/
theorem support_iff_forall_realize (M : Model W Domain Const Pred)
    {φ : Formula Var Const Pred}
    {τ : ModalFormula ((Language.monadic Pred)[[Const]]) Var}
    (hτ : φ.toModal? = some τ) (s : Finset (Index W Var Domain))
    (v : Index W Var Domain → Var → Domain)
    (hv : ∀ i ∈ s, ∀ y, i.assign y = ↑(v i y)) :
    support M φ s ↔ ∀ i ∈ s, τ.Realize M i.world (v i) := by
  rw [support_iff_forall_singleton (neFree_of_toModal? hτ)]
  exact forall₂_congr fun i hi ↦
    support_singleton_iff_realize M hτ (hv i hi)

end Realize

end QBSML
