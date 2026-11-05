module

public import Linglib.Logic.Team.BSML.Defs

/-!
# Negation in BSML

BSML's negation swaps support and anti-support. It validates double negation elimination, the
De Morgan laws and the duality of `◇` and `□` as strong equivalences (`⊜`, same support and same
anti-support), and a team supporting a formula is disjoint from every team anti-supporting it. It
is not a function of support alone: two formulas with the same support can have negations with
different support, so replacement of equivalents fails under `¬`, while strongly equivalent
formulas replace each other everywhere. Aloni states these facts for BSML; Aloni, Anttila and
Yang distinguish equivalence from strong equivalence.

## Main results

* `stronglyEquivalent_neg_neg`, `stronglyEquivalent_neg_conj`, `stronglyEquivalent_neg_disj`,
  `stronglyEquivalent_neg_poss`, `stronglyEquivalent_neg_nec`: the classical laws of negation.
* `disjoint_of_support_of_antiSupport`: negation is incompatibility.
* `exists_equivalent_not_equivalent_neg`: replacement of equivalents fails under negation.
* `StronglyEquivalent.subst`: strongly equivalent formulas can replace each other.

## Implementation notes

The laws hold by `rfl` as identities of meaning: negation is the involution of
`Truthmaker.BilProp`, the anti-support clause of each connective is the support clause of its
De Morgan dual, and `□` abbreviates `¬◇¬`. Replacement is the compositionality of
`Formula.den`.

## References

* [aloni-2022] Aloni, Logic and Conversation: The Case of Free Choice
* [aloni-anttila-yang-2024] Aloni, Anttila and Yang, State-based Modal Logics for Free Choice
* [anttila-2021] Anttila, The Logic of Free Choice: Axiomatizations of State-based Modal Logics
-/

public section

namespace BSML

open ModalLogic (KripkeModel)

variable {W : Type*} [DecidableEq W] {Atom : Type*}

/-! ### The classical laws -/

section Laws

variable (φ ψ : Formula Atom)

/-- Double negation elimination holds as a strong equivalence, `¬¬φ ⊜ φ` ([aloni-2022] Fact 6,
    [aloni-anttila-yang-2024] Fact 2.5). -/
theorem stronglyEquivalent_neg_neg : StronglyEquivalent (W := W) (.neg (.neg φ)) φ :=
  stronglyEquivalent_iff.2 fun _ ↦ rfl

/-- The negation of a conjunction is the split disjunction of the negations,
    `¬(φ ∧ ψ) ⊜ ¬φ ∨ ¬ψ` ([aloni-2022] Fact 6, [aloni-anttila-yang-2024] Fact 2.5). -/
theorem stronglyEquivalent_neg_conj :
    StronglyEquivalent (W := W) (.neg (.conj φ ψ)) (.disj (.neg φ) (.neg ψ)) :=
  stronglyEquivalent_iff.2 fun _ ↦ rfl

/-- The negation of a split disjunction is the conjunction of the negations,
    `¬(φ ∨ ψ) ⊜ ¬φ ∧ ¬ψ` ([aloni-2022] Fact 6, [aloni-anttila-yang-2024] Fact 2.5). -/
theorem stronglyEquivalent_neg_disj :
    StronglyEquivalent (W := W) (.neg (.disj φ ψ)) (.conj (.neg φ) (.neg ψ)) :=
  stronglyEquivalent_iff.2 fun _ ↦ rfl

/-- Negation turns `◇` into `□`, `¬◇φ ⊜ □¬φ` ([aloni-2022] Fact 6,
    [aloni-anttila-yang-2024] Fact 2.5). -/
theorem stronglyEquivalent_neg_poss :
    StronglyEquivalent (W := W) (.neg (.poss φ)) (Formula.nec (.neg φ)) :=
  stronglyEquivalent_iff.2 fun _ ↦ rfl

/-- Negation turns `□` into `◇`, `¬□φ ⊜ ◇¬φ` ([aloni-2022] Fact 6). -/
theorem stronglyEquivalent_neg_nec :
    StronglyEquivalent (W := W) (.neg φ.nec) (.poss (.neg φ)) :=
  stronglyEquivalent_iff.2 fun _ ↦ rfl

end Laws

/-! ### Negation and incompatibility -/

variable {M : KripkeModel W Atom} {φ : Formula Atom} {s t : Finset W}

/-- A team supporting `φ` and a team anti-supporting `φ` are disjoint ([aloni-2022] Fact 7,
    [anttila-2021] Proposition 3.3.9). -/
theorem disjoint_of_support_of_antiSupport (hs : support M φ s) (ht : antiSupport M φ t) :
    Disjoint s t := by
  induction φ generalizing s t with
  | atom p =>
    exact Finset.disjoint_left.mpr fun w hw hw' ↦ ht w hw' (hs w hw)
  | ne => exact ht ▸ Finset.disjoint_empty_right s
  | neg ψ ih => exact (ih ht hs).symm
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨t₁, h₁, t₂, h₂, rfl⟩ := ht
    exact Finset.disjoint_union_right.mpr ⟨ih₁ hs.1 h₁, ih₂ hs.2 h₂⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨s₁, h₁, s₂, h₂, rfl⟩ := hs
    exact Finset.disjoint_union_left.mpr ⟨ih₁ h₁ ht.1, ih₂ h₂ ht.2⟩
  | poss ψ ih =>
    refine Finset.disjoint_left.mpr fun w hw hw' ↦ ?_
    obtain ⟨u, ⟨hsu, v, hv⟩, hu⟩ := hs w hw
    exact Finset.disjoint_left.mp (ih hsu (ht w hw')) hv (hu hv)

/-- A team that supports and anti-supports `φ` is empty ([anttila-2021] Proposition 3.3.9). -/
theorem eq_empty_of_support_of_antiSupport (hs : support M φ s) (hs' : antiSupport M φ s) :
    s = ∅ :=
  (Finset.disjoint_self_iff_empty s).mp (disjoint_of_support_of_antiSupport hs hs')

/-! ### Failure of replacement under negation -/

/-- Replacement of equivalents fails under negation, as `p ∧ ¬p` and `¬NE` are equivalent but their
negations are not ([aloni-2022] Fact 8, [anttila-2021] Fact 2.2.3). -/
theorem exists_equivalent_not_equivalent_neg [Inhabited Atom] :
    ∃ φ ψ : Formula Atom, Equivalent (W := W) φ ψ ∧ ¬ Equivalent (W := W) (.neg φ) (.neg ψ) :=
  ⟨.falsum, .neg .ne, fun M t ↦ (support_falsum M t).trans .rfl,
    fun h ↦ Finset.not_nonempty_empty <| (h ⟨fun _ ↦ ∅, fun _ _ ↦ false⟩ ∅).mp
      ⟨∅, Team.empty_mem_flat _, ∅, Team.empty_mem_flat _, Finset.union_empty ∅⟩⟩

/-! ### Replacement of strong equivalents -/

/-- `θ.subst p φ` replaces every occurrence of the atom `p` in `θ` by `φ`. -/
def Formula.subst [DecidableEq Atom] : Formula Atom → Atom → Formula Atom → Formula Atom
  | .atom q, p, φ => if q = p then φ else .atom q
  | .ne, _, _ => .ne
  | .neg θ, p, φ => .neg (θ.subst p φ)
  | .conj θ η, p, φ => .conj (θ.subst p φ) (η.subst p φ)
  | .disj θ η, p, φ => .disj (θ.subst p φ) (η.subst p φ)
  | .poss θ, p, φ => .poss (θ.subst p φ)

/-- Substituting strongly equivalent formulas for an atom yields strongly equivalent formulas
([aloni-anttila-yang-2024] Proposition 2.4). -/
theorem StronglyEquivalent.subst [DecidableEq Atom] {ψ : Formula Atom}
    (h : StronglyEquivalent (W := W) φ ψ) (θ : Formula Atom) (p : Atom) :
    StronglyEquivalent (W := W) (θ.subst p φ) (θ.subst p ψ) := by
  rw [stronglyEquivalent_iff] at h ⊢
  intro M
  induction θ with
  | atom q => by_cases hq : q = p <;> simp [Formula.subst, hq, h M]
  | ne => rfl
  | neg θ ih => exact congrArg Neg.neg ih
  | conj θ η ih₁ ih₂ | disj θ η ih₁ ih₂ => simp only [Formula.subst, Formula.den, ih₁, ih₂]
  | poss θ ih => simp only [Formula.subst, Formula.den, ih]

end BSML
