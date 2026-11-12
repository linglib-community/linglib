module

public import Linglib.Logic.Orthologic.Epistemic.Basic
public import Linglib.Logic.Orthologic.Epistemic.Compatibility
public import Linglib.Core.Order.Ortholattice.ProperFilter

/-!
# Frame semantics and completeness for the epistemic orthologic

This file proves that [EO is sound and complete for epistemic compatibility
frames](##Orthologic.ModalFormula.derivable_iff_frameConsequence). A possibility supports `□φ`
when every possibility it accesses supports `φ`, so [the supporters of a formula are its
value](##Orthologic.ModalFormula.support_setOf_eq_coe_eval) in the ortholattice of regular
propositions, and soundness is algebraic soundness. For completeness, Goldblatt's frame of proper
filters of an epistemic ortholattice, with the accessibility relation of its `□`, is [R-regular
and knowable](##Orthologic.Compatibility.isKnowable_ofFilters), and [sending an element to the
filters containing it embeds the ortholattice with its `□`](##Orthologic.Compatibility.embed_box).

## Implementation notes

The non-modal completeness proof in `Logic/Orthologic/FrameSemantics.lean` represents an
ortholattice by its elements. The filters `{c | □c ∈ F}` that the modal proof needs are proper but
in general not principal, so the canonical frame here is built on the proper-filter
representation of `Core/Order/Ortholattice/ProperFilter.lean`.

## References

* [goldblatt-1975]
* [holliday-mandelkern-2024]
-/

@[expose] public section

open Order Concept SetRel

universe u

namespace Orthologic

/-! ### Support in a modal compatibility model -/

namespace ModalFormula

variable {Var : Type u} {S : Type u}

/-- Support in the modal compatibility model `(F, R, V)`: the clauses for orthologic, and `s`
supports `□φ` when every possibility it accesses supports `φ` ([holliday-mandelkern-2024]
Definition 4.31). -/
def Support (F : Compatibility S) (R : SetRel S S) (V : Var → F.Regular) (s : S) :
    ModalFormula Var → Prop
  | .top => True
  | .var p => s ∈ V p
  | .neg φ => ∀ t, F.compat s t → ¬ Support F R V t φ
  | .and φ ψ => Support F R V s φ ∧ Support F R V s ψ
  | .box φ => ∀ t, s ~[R] t → Support F R V t φ

/-- Over an R-regular frame the supporters of `φ` are its value in the modal ortholattice of
regular propositions, so in particular they form a regular set ([holliday-mandelkern-2024]
Lemma 4.32). -/
theorem support_setOf_eq_coe_eval (F : Compatibility S) (R : SetRel S S) [IsRRegular F R]
    (V : Var → F.Regular) (φ : ModalFormula Var) :
    {s | Support F R V s φ} = ((eval (F.necHom R) V φ : F.Regular) : Set S) := by
  induction φ with
  | top => rfl
  | var p => rfl
  | neg φ ih =>
    rw [eval, Concept.coe_compl, ← ih]
    exact Set.ext fun _ ↦ F.mem_upperPolar_ortho.symm
  | and φ ψ ihφ ihψ =>
    rw [eval, Concept.coe_inf, ← ihφ, ← ihψ]
    rfl
  | box φ ih =>
    rw [eval, Compatibility.coe_necHom, ← ih]
    rfl

/-! ### Consequence over epistemic compatibility frames -/

variable {φ ψ : ModalFormula Var}

variable (φ ψ) in
/-- `ψ` is a consequence of `φ` over epistemic compatibility frames, the R-regular, reflexive
frames with Knowability, when in every model on such a frame every possibility supporting `φ`
supports `ψ` ([holliday-mandelkern-2024] Definition 4.36 for the class of Definition 4.26). -/
def FrameConsequence : Prop :=
  ∀ {S : Type u} (F : Compatibility S) (R : SetRel S S) [IsRRegular F R] [R.IsRefl]
    [IsKnowable F R] (V : Var → F.Regular) (s : S), Support F R V s φ → Support F R V s ψ

theorem frameConsequence_iff_eval :
    FrameConsequence φ ψ ↔ ∀ {S : Type u} (F : Compatibility S) (R : SetRel S S)
      [IsRRegular F R] [R.IsRefl] [IsKnowable F R] (V : Var → F.Regular),
        eval (F.necHom R) V φ ≤ eval (F.necHom R) V ψ := by
  refine ⟨fun h S F R _ _ _ V ↦ ?_, fun h S F R _ _ _ V s hs ↦ ?_⟩
  · rw [← SetLike.coe_subset_coe, ← support_setOf_eq_coe_eval, ← support_setOf_eq_coe_eval]
    exact fun s hs ↦ h F R V s hs
  · have hsub := SetLike.coe_subset_coe.mpr (h F R V)
    rw [← support_setOf_eq_coe_eval, ← support_setOf_eq_coe_eval] at hsub
    exact hsub hs

/-- EO is sound for epistemic compatibility frames ([holliday-mandelkern-2024] Theorem 4.37). -/
theorem frame_sound (h : EDerivable φ ψ) : FrameConsequence φ ψ :=
  frameConsequence_iff_eval.mpr fun F R _ _ _ V ↦ sound (Compatibility.isEpistemic_necHom F R) h V

end ModalFormula

/-! ### The canonical frame of proper filters -/

open ProperFilter

variable {L : Type*} [Lattice L] [BoundedOrder L] [InvolutiveCompl L] [IsOrtholattice L]

namespace Compatibility

variable (L) in
/-- The canonical frame of an ortholattice: its proper filters, compatible when not orthogonal
([goldblatt-1975]; [holliday-mandelkern-2024] proof of Theorem 4.37). -/
def ofFilters : Compatibility (ProperFilter L) where
  compat F G := ¬ ProperFilter.Orthogonal F G
  compat_refl := ⟨fun F ↦ Std.Irrefl.irrefl (r := ProperFilter.Orthogonal) F⟩
  compat_symm := ⟨fun _ _ h h' ↦ h (Std.Symm.symm _ _ h')⟩
  ortho := ProperFilter.Orthogonal
  ortho_iff _ _ := not_not.symm

theorem ofFilters_compat {F G : ProperFilter L} :
    (ofFilters L).compat F G ↔ ∀ a ∈ F.1, aᶜ ∉ G.1 :=
  ⟨fun h a ha hac ↦ h ⟨a, ha, hac⟩, fun h ⟨a, ha, hac⟩ ↦ h a ha hac⟩

variable {box : InfTopHom L L}

/-- The canonical frame is R-regular: a possibility compatible with one according to which `G`
might obtain is given by the filter generated by `◇` of `G` ([holliday-mandelkern-2024] proof of
Theorem 4.37). -/
theorem isRRegular_ofFilters (hT : ∀ a, box a ≤ a) : IsRRegular (ofFilters L) (access box) := by
  refine (isRRegular_iff _ _).2 fun F G' G hFG' hG'G ↦ ?_
  let dia : L →o L := ⟨diamondHom box, OrderHomClass.mono _⟩
  have key : ∀ c ∈ F.1, cᶜ ∉ G.1.map dia := fun c hc hcD ↦ by
    obtain ⟨a, haG, hac⟩ := PFilter.mem_map.1 hcD
    have hbox : box aᶜ ∈ F.1 := F.1.mem_of_le (by
      simpa only [dia, OrderHom.coe_mk, diamondHom_apply, InvolutiveCompl.compl_compl] using
        InvolutiveCompl.le_compl_comm.mp hac) hc
    exact ofFilters_compat.1 hG'G aᶜ (mem_access.1 hFG' aᶜ hbox)
      (by rwa [InvolutiveCompl.compl_compl])
  refine ⟨⟨G.1.map dia, fun h ↦ key ⊤ F.1.top_mem ?_⟩, ofFilters_compat.2 key,
    fun H hDH ↦ ⟨nec hT H, access_nec hT H, ofFilters_compat.2 fun d hd hdG ↦
      ofFilters_compat.1 hDH (dia dᶜ) (PFilter.mem_map.2 ⟨dᶜ, hdG, le_rfl⟩) ?_⟩⟩
  · rwa [InvolutiveCompl.compl_top]
  · simpa only [dia, OrderHom.coe_mk, diamondHom_apply, InvolutiveCompl.compl_compl] using
      mem_nec.1 hd

/-- The canonical frame satisfies Knowability: everything accessible from the filter generated by
`□` of `F` refines `F`, and the filter is proper by Wittgenstein's Law
([holliday-mandelkern-2024] proof of Theorem 4.37). -/
theorem isKnowable_ofFilters (hE : IsEpistemic box) : IsKnowable (ofFilters L) (access box) := by
  let nb : L →o L := ⟨box, OrderHomClass.mono _⟩
  refine ⟨fun F ↦ ⟨⟨F.1.map nb, fun h ↦ ?_⟩, fun H hGH ↦ ?_⟩⟩
  · obtain ⟨a, haF, ha⟩ := PFilter.mem_map.1 h
    rw [hE.wittgensteinLaw.eq_bot_of_box_eq_bot (le_bot_iff.mp ha)] at haF
    exact F.2 haF
  · exact (ofFilters L).mem_ofObject_ortho.2 fun I hHI ↦ ofFilters_compat.2 fun c hc hcI ↦
      ofFilters_compat.1 hHI c (mem_access.1 hGH c (PFilter.mem_map.2 ⟨c, hc, le_rfl⟩)) hcI

/-- On the canonical frame of an epistemic ortholattice, `embed` commutes with `□`
([holliday-mandelkern-2024] proof of Theorem 4.37). -/
theorem embed_box [IsRRegular (ofFilters L) (access box)] (hT : ∀ a, box a ≤ a) (a : L) :
    embed (box a) = (ofFilters L).necHom (access box) (embed a) :=
  SetLike.coe_injective (core_setOf_mem hT a).symm

end Compatibility

/-! ### Completeness -/

namespace ModalFormula

open Compatibility

variable {Var : Type u} {φ ψ : ModalFormula Var}

theorem eval_embed {box : InfTopHom L L} [IsRRegular (ofFilters L) (access box)]
    (hT : ∀ a, box a ≤ a) (v : Var → L) (φ : ModalFormula Var) :
    eval ((ofFilters L).necHom (access box)) (fun p ↦ embed (v p)) φ = embed (eval box v φ) :=
  (map_eval embedHom (embed_box hT) v φ).symm

/-- Consequence over epistemic compatibility frames implies derivability in EO
([holliday-mandelkern-2024] Theorem 4.37). -/
theorem frame_complete (h : FrameConsequence φ ψ) : EDerivable φ ψ := by
  refine complete fun {L} _ _ _ _ box hE v ↦ ?_
  have := isRRegular_ofFilters hE.apply_le
  have := isRefl_access hE.apply_le
  have := isKnowable_ofFilters hE
  have hframe := frameConsequence_iff_eval.mp h (ofFilters L) (access box) fun p ↦ embed (v p)
  rw [eval_embed hE.apply_le, eval_embed hE.apply_le] at hframe
  exact embed_le_embed.mp hframe

/-- EO is sound and complete for epistemic compatibility frames ([holliday-mandelkern-2024]
Theorem 4.37). -/
theorem derivable_iff_frameConsequence : EDerivable φ ψ ↔ FrameConsequence φ ψ :=
  ⟨frame_sound, frame_complete⟩

end ModalFormula

end Orthologic
