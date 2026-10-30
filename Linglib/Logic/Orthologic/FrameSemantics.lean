module

public import Linglib.Logic.Orthologic.Basic
public import Linglib.Logic.Orthologic.CompatFrame
public import Linglib.Core.Order.Ortholattice.Representation

/-!
# Frame semantics and completeness for orthologic

This file proves Goldblatt's completeness theorem for orthologic over compatibility frames, in
the form Holliday and Mandelkern give it. A compatibility model is a frame `F` with a valuation
`V : Var → F.Regular` assigning each variable a regular proposition, and support `s ⊩ φ` is
defined recursively. The supporters of a formula are exactly its algebraic value in the
ortholattice of regular propositions, so frame consequence is the algebraic inequality in every
frame algebra. The representation of ortholattices places every ortholattice inside a frame
algebra, so frame validity entails validity in all ortholattices, and completeness follows from
algebraic completeness.

## Main definitions

* `Orthologic.Support`: support of a formula at a possibility of a compatibility model.
* `Orthologic.FrameConsequence`: consequence over all compatibility models.
* `Orthologic.CompatFrame.ofOrtholattice`: the canonical frame of an ortholattice.

## Main results

* `Orthologic.support_setOf_eq_coe_eval`: the supporters of `φ` are its algebraic value.
* `Orthologic.derivable_iff_frameConsequence`: derivability is frame consequence.

## References

* [holliday-mandelkern-2024]
* [maclaren-1964]
-/

@[expose] public section

open Order Set OrthoConcept

universe u

namespace Orthologic

variable {Var : Type u} {S : Type u}

/-! ### Support in a compatibility model -/

/-- Support in the compatibility model `(F, V)`: `s` supports `¬φ` when no possibility compatible
    with `s` supports `φ` ([holliday-mandelkern-2024] Definition 4.15). -/
def Support (F : CompatFrame S) (V : Var → F.Regular) (s : S) : Formula Var → Prop
  | .top => True
  | .var p => s ∈ V p
  | .neg φ => ∀ t, F.compat s t → ¬ Support F V t φ
  | .and φ ψ => Support F V s φ ∧ Support F V s ψ

/-- The supporters of `φ` are its algebraic value in the regular propositions, so in particular
    they form a regular set ([holliday-mandelkern-2024] Lemma 4.16). -/
theorem support_setOf_eq_coe_eval (F : CompatFrame S) (V : Var → F.Regular) (φ : Formula Var) :
    {s | Support F V s φ} = ((Formula.eval V φ : F.Regular) : Set S) := by
  induction φ with
  | top => rfl
  | var p => rfl
  | neg φ ih =>
    rw [show Formula.eval V φ.neg = (Formula.eval V φ)ᶜ from rfl, CompatFrame.Regular.coe_compl,
      ← ih]
    rfl
  | and φ ψ ihφ ihψ =>
    rw [show Formula.eval V (φ.and ψ) = Formula.eval V φ ⊓ Formula.eval V ψ from rfl,
      CompatFrame.Regular.coe_inf, ← ihφ, ← ihψ]
    rfl

/-! ### Frame consequence, soundness, completeness -/

/-- `ψ` is a semantic consequence of `φ` over compatibility frames when in every model every
    possibility supporting `φ` supports `ψ` ([holliday-mandelkern-2024] Definition 4.18). -/
def FrameConsequence (φ ψ : Formula Var) : Prop :=
  ∀ {S : Type u} (F : CompatFrame S) (V : Var → F.Regular) (s : S),
    Support F V s φ → Support F V s ψ

@[inherit_doc] scoped infix:50 " ⊨ᶠ " => FrameConsequence

theorem frameConsequence_iff_eval {φ ψ : Formula Var} :
    (φ ⊨ᶠ ψ) ↔ ∀ {S : Type u} (F : CompatFrame S) (V : Var → F.Regular),
      Formula.eval V φ ≤ Formula.eval V ψ := by
  refine ⟨fun h S F V ↦ ?_, fun h S F V s hs ↦ ?_⟩
  · rw [← SetLike.coe_subset_coe, ← support_setOf_eq_coe_eval, ← support_setOf_eq_coe_eval]
    exact fun s hs ↦ h F V s hs
  · have hsub := SetLike.coe_subset_coe.mpr (h F V)
    rw [← support_setOf_eq_coe_eval, ← support_setOf_eq_coe_eval] at hsub
    exact hsub hs

/-- Derivability is sound for frame consequence ([holliday-mandelkern-2024] Theorem 4.19). -/
theorem frame_sound {φ ψ : Formula Var} (h : φ ⊢ ψ) : φ ⊨ᶠ ψ :=
  frameConsequence_iff_eval.mpr fun _ V ↦ sound h V

/-- The canonical frame of an ortholattice over `V`: two nonzero elements of `V` are compatible
    when neither lies below the complement of the other, the representation of [maclaren-1964]
    ([holliday-mandelkern-2024] Theorem 4.13). -/
def CompatFrame.ofOrtholattice {L : Type*} [Lattice L] [BoundedOrder L] [InvolutiveCompl L]
    [IsOrtholattice L] (V : Set L) : CompatFrame (Point V) where
  compat a b := ¬ Orthogonal V a b
  compat_refl := ⟨fun a ↦ Std.Irrefl.irrefl (r := Orthogonal V) a⟩
  compat_symm := ⟨fun _ _ h h' ↦ h (Std.Symm.symm _ _ h')⟩
  ortho := Orthogonal V
  ortho_iff _ _ := not_not.symm

@[simp] theorem CompatFrame.ofOrtholattice_compat {L : Type*} [Lattice L] [BoundedOrder L]
    [InvolutiveCompl L] [IsOrtholattice L] {V : Set L} {a b : Point V} :
    (CompatFrame.ofOrtholattice V).compat a b ↔ ¬ a.1 ≤ b.1ᶜ := Iff.rfl

theorem eval_map {L : Type u} [Lattice L] [BoundedOrder L] [InvolutiveCompl L]
    [IsOrtholattice L] {V₀ : Set L} (hV : JoinDense V₀) (v : Var → L) (φ : Formula Var) :
    Formula.eval (fun p ↦ principal V₀ (v p)) φ = principal V₀ (Formula.eval v φ) := by
  induction φ with
  | top => simp only [Formula.eval, principal_top hV]
  | var p => rfl
  | neg φ ih => simp only [Formula.eval, ih, principal_compl hV]
  | and φ ψ ihφ ihψ => simp only [Formula.eval, ihφ, ihψ, principal_inf hV]

/-- Frame consequence implies derivability ([holliday-mandelkern-2024] Theorem 4.19). -/
theorem frame_complete {φ ψ : Formula Var} (h : φ ⊨ᶠ ψ) : φ ⊢ ψ := by
  apply Orthologic.complete
  intro L _ _ _ _ v
  have hjd : JoinDense (Set.univ : Set L) := fun a ↦ (Set.univ_inter (Set.Iic a)).symm ▸ isLUB_Iic
  have hframe := frameConsequence_iff_eval.mp h (CompatFrame.ofOrtholattice (Set.univ : Set L))
    fun p ↦ principal Set.univ (v p)
  rw [eval_map hjd, eval_map hjd] at hframe
  exact (principal_le_principal hjd).mp hframe

/-- Derivability is consequence over all compatibility frames, Goldblatt's completeness theorem
    ([holliday-mandelkern-2024] Theorem 4.19). -/
theorem derivable_iff_frameConsequence {φ ψ : Formula Var} :
    φ ⊢ ψ ↔ φ ⊨ᶠ ψ :=
  ⟨frame_sound, frame_complete⟩

end Orthologic
