module

public import Linglib.Logic.Team.BSML.Defs
public import Linglib.Logic.Modal.Defs

/-!
# The classical fragment of BSML

The `NE`-free fragment of BSML, Aloni's BSML∅, behaves like classical modal logic. A BSML
formula is classically true at a single world, `Realize`, with the modal clause taken from
`ModalLogic.Diamond`, and on `NE`-free formulas team support is classical truth at every world
of the team, in both polarities. Consequence and equivalence then coincide with their classical
definitions, as Aloni and Anttila observe.

## Main definitions

* `Realize M φ w`: classical truth of `φ` at the world `w` of `M`.
* `ClassicalConsequence`: classical modal consequence.

## Main results

* `eval_iff_forall_realize`, `support_iff_forall_realize`,
  `antiSupport_iff_forall_not_realize`: an `NE`-free formula is supported by a team iff it is
  true at each of its worlds, and anti-supported iff false at each.
* `support_singleton_iff_realize`: the singleton case, `{w} ⊨⁺ φ ↔ M, w ⊨ φ`.
* `consequence_iff_classicalConsequence`: on `NE`-free formulas, BSML consequence is
  classical modal consequence.
* `equivalent_iff_classicalConsequence`: on `NE`-free formulas, equivalence is mutual
  classical consequence.

## Implementation notes

`Realize` is total: `NE` is true at every world, since singletons are non-empty, so the
equations of Proposition 2.2.16 are stated for `NE`-free formulas only, as in the sources.
The proposition is one induction over the polarity parameter of `eval`, with the split
clauses discharged by `Team.mem_tensor_flat` and the `◇`-support clause by
`Team.exists_nonempty_subset_forall_iff`. The sources derive the proposition from the flatness
of the `NE`-free fragment; here flatness is derived from it (`isFlat_support_of_neFree`).

## References

* [aloni-2022] Aloni, Logic and Conversation: The Case of Free Choice
* [anttila-2021] Anttila, The Logic of Free Choice: Axiomatizations of State-based Modal
  Logics
-/

@[expose] public section

namespace BSML

open ModalLogic (KripkeModel)
open scoped ModalLogic

variable {W : Type*} {Atom : Type*}

/-! ### Classical truth -/

/-- `Realize M φ w` is the classical Kripke truth of `φ` at the world `w`. Split disjunction is
    pointwise, `◇` is `ModalLogic.Diamond` over `M.accessible`, and `NE` is true. -/
def Realize (M : KripkeModel W Atom) : Formula Atom → W → Prop
  | .atom p, w => M.val p w
  | .ne, _ => True
  | .neg ψ, w => ¬ Realize M ψ w
  | .conj ψ₁ ψ₂, w => Realize M ψ₁ w ∧ Realize M ψ₂ w
  | .disj ψ₁ ψ₂, w => Realize M ψ₁ w ∨ Realize M ψ₂ w
  | .poss ψ, w => ◇[M.accessible] (Realize M ψ) w

instance instDecidableRealize (M : KripkeModel W Atom) [DecidableRel M.val] :
    (φ : Formula Atom) → (w : W) → Decidable (Realize M φ w)
  | .atom p, w => inferInstanceAs (Decidable (M.val p w))
  | .ne, _ => .isTrue trivial
  | .neg ψ, w => @instDecidableNot _ (instDecidableRealize M ψ w)
  | .conj ψ₁ ψ₂, w =>
    @instDecidableAnd _ _ (instDecidableRealize M ψ₁ w) (instDecidableRealize M ψ₂ w)
  | .disj ψ₁ ψ₂, w =>
    @instDecidableOr _ _ (instDecidableRealize M ψ₁ w) (instDecidableRealize M ψ₂ w)
  | .poss ψ, w =>
    @Finset.decidableExistsAndFinset _ (M.access w) _ (fun v ↦ instDecidableRealize M ψ v)

variable {M : KripkeModel W Atom} {φ ψ ψ₁ ψ₂ : Formula Atom} {w : W}

@[simp] theorem realize_atom {p : Atom} : Realize M (.atom p) w ↔ M.val p w := Iff.rfl

@[simp] theorem realize_ne : Realize M .ne w := trivial

@[simp] theorem realize_neg : Realize M (.neg ψ) w ↔ ¬ Realize M ψ w := Iff.rfl

@[simp] theorem realize_conj :
    Realize M (.conj ψ₁ ψ₂) w ↔ Realize M ψ₁ w ∧ Realize M ψ₂ w := Iff.rfl

@[simp] theorem realize_disj :
    Realize M (.disj ψ₁ ψ₂) w ↔ Realize M ψ₁ w ∨ Realize M ψ₂ w := Iff.rfl

theorem realize_poss : Realize M (.poss ψ) w ↔ ∃ v ∈ M.access w, Realize M ψ v := Iff.rfl

theorem realize_nec : Realize M ψ.nec w ↔ □[M.accessible] (Realize M ψ) w := by
  simp [Formula.nec, Realize]

/-! ### Support is pointwise truth (Proposition 2.2.16) -/

variable [DecidableEq W] {t : Finset W}

/-- An `NE`-free formula is supported (anti-supported) by `t` iff it is true (false) at every world
of `t` ([anttila-2021] Proposition 2.2.16). -/
theorem eval_iff_forall_realize (hNE : φ.NEFree) (b : Bool) (t : Finset W) :
    eval M b φ t ↔ ∀ w ∈ t, (Realize M φ w ↔ b) := by
  induction φ generalizing b t with
  | atom p => cases b <;> simp [eval, Realize]
  | ne => exact hNE.elim
  | neg ψ ih =>
    cases b
    · simpa [eval, Realize] using ih hNE true t
    · simpa [eval, Realize] using ih hNE false t
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    cases b
    · simp only [eval, ih₁ hNE.1, ih₂ hNE.2]
      refine Team.mem_tensor_flat.trans ?_
      simp [Realize, imp_iff_not_or]
    · simp [eval, ih₁ hNE.1, ih₂ hNE.2, Realize, forall_and]
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    cases b
    · simp [eval, ih₁ hNE.1, ih₂ hNE.2, Realize, forall_and, not_or]
    · simp only [eval, ih₁ hNE.1, ih₂ hNE.2]
      refine Team.mem_tensor_flat.trans ?_
      simp [Realize]
  | poss ψ ih =>
    cases b
    · simp [eval, ih hNE, realize_poss]
    · simp [eval, ih hNE, Team.exists_nonempty_subset_forall_iff, realize_poss]

theorem support_iff_forall_realize (hNE : φ.NEFree) :
    support M φ t ↔ ∀ w ∈ t, Realize M φ w := by
  simpa using eval_iff_forall_realize hNE true t

theorem antiSupport_iff_forall_not_realize (hNE : φ.NEFree) :
    antiSupport M φ t ↔ ∀ w ∈ t, ¬ Realize M φ w := by
  simpa using eval_iff_forall_realize hNE false t

/-- A singleton team supports an `NE`-free formula iff its world realizes it,
    `{w} ⊨⁺ φ ↔ M, w ⊨ φ`. -/
theorem support_singleton_iff_realize (hNE : φ.NEFree) :
    support M φ {w} ↔ Realize M φ w := by
  simp [support_iff_forall_realize hNE]

theorem antiSupport_singleton_iff_not_realize (hNE : φ.NEFree) :
    antiSupport M φ {w} ↔ ¬ Realize M φ w := by
  simp [antiSupport_iff_forall_not_realize hNE]

/-! ### Consequence is classical consequence (Fact 15) -/

/-- `ψ` is a classical modal consequence of `φ` when every world of every model realizing `φ`
    realizes `ψ`. -/
def ClassicalConsequence (φ ψ : Formula Atom) : Prop :=
  ∀ (M : KripkeModel W Atom) (w : W), Realize M φ w → Realize M ψ w

/-- On `NE`-free formulas BSML consequence is classical modal consequence ([aloni-2022] Fact 15,
    [anttila-2021] Fact 2.2.17). -/
theorem consequence_iff_classicalConsequence (hφ : φ.NEFree) (hψ : ψ.NEFree) :
    Consequence (W := W) φ ψ ↔ ClassicalConsequence (W := W) φ ψ where
  mp h M w hw :=
    (support_singleton_iff_realize hψ).mp (h M {w} ((support_singleton_iff_realize hφ).mpr hw))
  mpr h M _ ht :=
    (support_iff_forall_realize hψ).mpr fun w hw ↦
      h M w ((support_iff_forall_realize hφ).mp ht w hw)

/-- On `NE`-free formulas equivalence is mutual classical consequence ([anttila-2021]
    Fact 2.2.17). -/
theorem equivalent_iff_classicalConsequence (hφ : φ.NEFree) (hψ : ψ.NEFree) :
    Equivalent (W := W) φ ψ ↔
      ClassicalConsequence (W := W) φ ψ ∧ ClassicalConsequence (W := W) ψ φ :=
  equivalent_iff.trans <| and_congr (consequence_iff_classicalConsequence hφ hψ)
    (consequence_iff_classicalConsequence hψ hφ)

end BSML
