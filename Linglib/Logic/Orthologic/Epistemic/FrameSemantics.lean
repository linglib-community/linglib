module

public import Linglib.Logic.Orthologic.Epistemic.Basic
public import Linglib.Logic.Orthologic.Epistemic.Compatibility
public import Mathlib.Order.PFilter

/-!
# Frame semantics and completeness for the epistemic orthologic

This file proves that [EO is sound and complete for epistemic compatibility
frames](##Orthologic.ModalFormula.derivable_iff_frameConsequence). A possibility supports `□φ`
when every possibility it accesses supports `φ`, so [the supporters of a formula are its
value](##Orthologic.ModalFormula.support_setOf_eq_coe_eval) in the ortholattice of regular
propositions, and soundness is algebraic soundness. For completeness, the proper filters of an
epistemic ortholattice form [an epistemic compatibility
frame](##Orthologic.Compatibility.ofFilters), and [sending an element to the filters containing it
embeds the ortholattice with its `□`](##Orthologic.Compatibility.filterEmbed_box).

## Implementation notes

The non-modal completeness proof in `Logic/Orthologic/FrameSemantics.lean` represents an
ortholattice by its elements, MacLaren's points. That cannot carry `□`: at the point `a` the
accessible points would have to lie below every `c` with `a ≤ □c`, a meet the lattice need not
have. The filters `{c | □c ∈ F}` that the modal proof needs are proper filters but not in general
principal, so the canonical frame here is Goldblatt's frame of all proper filters.

## References

* [goldblatt-1975]
* [holliday-mandelkern-2024]
* [maclaren-1964]
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

/-- The proper filters of `L`, the possibilities of its canonical frame. -/
abbrev ProperFilter (L : Type*) [Lattice L] [OrderBot L] : Type _ :=
  {F : PFilter L // ⊥ ∉ F}

variable {L : Type*} [Lattice L] [BoundedOrder L]

namespace ProperFilter

/-- The principal filter of a nonzero element. -/
def principal {a : L} (ha : a ≠ ⊥) : ProperFilter L :=
  ⟨PFilter.principal a, fun h ↦ ha (le_bot_iff.mp h)⟩

@[simp] theorem mem_principal {a b : L} (ha : a ≠ ⊥) : b ∈ (principal ha).1 ↔ a ≤ b := Iff.rfl

/-- The upward closure of the image of a filter under a monotone map is a filter. -/
def upMap (f : L → L) (hf : Monotone f) (G : PFilter L) : PFilter L :=
  IsPFilter.toPFilter <| IsPFilter.of_def (F := {b | ∃ a ∈ G, f a ≤ b}) ⟨f ⊤, ⊤, G.top_mem, le_rfl⟩
    (fun _ ⟨a, ha, hab⟩ _ ⟨a', ha', hab'⟩ ↦ ⟨f (a ⊓ a'), ⟨_, G.inf_mem ha ha', le_rfl⟩,
      (hf inf_le_left).trans hab, (hf inf_le_right).trans hab'⟩)
    fun hxy ⟨a, ha, hax⟩ ↦ ⟨a, ha, hax.trans hxy⟩

theorem mem_upMap {f : L → L} {hf : Monotone f} {G : PFilter L} {b : L} :
    b ∈ upMap f hf G ↔ ∃ a ∈ G, f a ≤ b := Iff.rfl

/-- The preimage of a filter under a map preserving `⊓` and `⊤` is a filter. -/
def comap (f : InfTopHom L L) (G : PFilter L) : PFilter L :=
  IsPFilter.toPFilter <| IsPFilter.of_def (F := {a | f a ∈ G}) ⟨⊤, by simp⟩
    (fun a ha a' ha' ↦ ⟨a ⊓ a', by simpa [map_inf] using G.inf_mem ha ha', inf_le_left,
      inf_le_right⟩)
    fun hxy h ↦ PFilter.mem_of_le (OrderHomClass.mono f hxy) h

theorem mem_comap {f : InfTopHom L L} {G : PFilter L} {a : L} : a ∈ comap f G ↔ f a ∈ G :=
  Iff.rfl

variable {box : InfTopHom L L}

/-- `{a | □a ∈ F}`, a proper filter when `□` is factive ([holliday-mandelkern-2024] proof of
Theorem 4.37). -/
def nec (hT : ∀ a, box a ≤ a) (F : ProperFilter L) : ProperFilter L :=
  ⟨comap box F.1, fun h ↦ F.2 <| by
    have h' := mem_comap.mp h
    rwa [le_bot_iff.mp (hT ⊥)] at h'⟩

theorem mem_nec {hT : ∀ a, box a ≤ a} {F : ProperFilter L} {a : L} :
    a ∈ (nec hT F).1 ↔ box a ∈ F.1 := Iff.rfl

variable (box) in
/-- Canonical accessibility: `F` accesses `G` when `G` contains everything necessary at `F`
([holliday-mandelkern-2024] proof of Theorem 4.37). -/
def access : SetRel (ProperFilter L) (ProperFilter L) :=
  {p | ∀ a, box a ∈ p.1.1 → a ∈ p.2.1}

theorem mem_access {F G : ProperFilter L} : F ~[access box] G ↔ ∀ a, box a ∈ F.1 → a ∈ G.1 :=
  Iff.rfl

theorem access_nec (hT : ∀ a, box a ≤ a) (F : ProperFilter L) : F ~[access box] nec hT F :=
  mem_access.2 fun _ h ↦ mem_nec.2 h

/-- `□` of the filters containing `a` is the filters containing `□a`. -/
theorem core_setOf_mem (hT : ∀ a, box a ≤ a) (a : L) :
    (access box).core {F : ProperFilter L | a ∈ F.1} = {F | box a ∈ F.1} :=
  Set.ext fun F ↦ ⟨fun h ↦ mem_nec.1 (show a ∈ (nec hT F).1 from h (access_nec hT F)),
    fun h _ hFG ↦ mem_access.1 hFG a h⟩

theorem isRefl_access (hT : ∀ a, box a ≤ a) : (access box).IsRefl :=
  ⟨fun F ↦ mem_access.2 fun a h ↦ F.1.mem_of_le (hT a) h⟩

end ProperFilter

open ProperFilter

variable [InvolutiveCompl L] [IsOrtholattice L]

namespace Compatibility

variable (L) in
/-- The canonical frame of an ortholattice: its proper filters, two compatible when neither
contains the complement of an element of the other ([goldblatt-1975]; [holliday-mandelkern-2024]
proof of Theorem 4.37). -/
def ofFilters : Compatibility (ProperFilter L) where
  compat F G := ∀ a ∈ F.1, aᶜ ∉ G.1
  compat_refl := ⟨fun F a ha hac ↦ F.2 <| by
    have h := F.1.inf_mem ha hac
    rwa [IsOrtholattice.inf_compl_eq_bot] at h⟩
  compat_symm := ⟨fun _ _ h b hb hbc ↦ h _ hbc (by rwa [InvolutiveCompl.compl_compl])⟩

theorem ofFilters_compat {F G : ProperFilter L} :
    (ofFilters L).compat F G ↔ ∀ a ∈ F.1, aᶜ ∉ G.1 := Iff.rfl

theorem isExtent_setOf_mem (a : L) :
    IsExtent (ofFilters L).ortho {F : ProperFilter L | a ∈ F.1} := by
  refine ((ofFilters L).isExtent_ortho_iff _).2 fun F ↦ or_iff_not_imp_left.2 fun haF ↦ ?_
  have hac : aᶜ ≠ ⊥ := fun h ↦ haF <| by
    rw [← InvolutiveCompl.compl_compl a, h, InvolutiveCompl.compl_bot]; exact F.1.top_mem
  refine ⟨principal hac, ofFilters_compat.2 fun c hc hca ↦ haF (F.1.mem_of_le ?_ hc),
    fun H hH haH ↦ ?_⟩
  · exact InvolutiveCompl.compl_le_compl_iff_le.mp ((mem_principal hac).1 hca)
  · exact ofFilters_compat.1 hH aᶜ ((mem_principal hac).2 le_rfl)
      (by rwa [InvolutiveCompl.compl_compl])

/-- The regular proposition of the filters containing `a`. -/
def filterEmbed (a : L) : (ofFilters L).Regular :=
  .ofIsExtent _ _ (isExtent_setOf_mem a)

@[simp] theorem coe_filterEmbed (a : L) :
    (filterEmbed a : Set (ProperFilter L)) = {F | a ∈ F.1} := rfl

theorem filterEmbed_le_filterEmbed {a b : L} : filterEmbed a ≤ filterEmbed b ↔ a ≤ b := by
  refine ⟨fun h ↦ ?_, fun h F hF ↦ F.1.mem_of_le h hF⟩
  rcases eq_or_ne a ⊥ with rfl | ha
  · exact bot_le
  · have hmem : principal ha ∈ (filterEmbed b : Set (ProperFilter L)) :=
      SetLike.coe_subset_coe.mpr h ((mem_principal ha).2 le_rfl)
    exact (mem_principal ha).1 hmem

theorem filterEmbed_inf (a b : L) : filterEmbed (a ⊓ b) = filterEmbed a ⊓ filterEmbed b :=
  SetLike.coe_injective <| by
    rw [Concept.coe_inf, coe_filterEmbed, coe_filterEmbed, coe_filterEmbed]
    exact Set.ext fun F ↦ F.1.inf_mem_iff (x := a) (y := b)

theorem filterEmbed_top : filterEmbed (⊤ : L) = ⊤ :=
  SetLike.coe_injective <| by
    rw [coe_filterEmbed, Concept.coe_top]
    exact Set.ext fun F ↦ iff_of_true F.1.top_mem trivial

theorem filterEmbed_compl (a : L) : filterEmbed aᶜ = (filterEmbed a)ᶜ := by
  refine SetLike.coe_injective <| Set.ext fun F ↦ ?_
  rw [Concept.coe_compl, coe_filterEmbed, (ofFilters L).mem_upperPolar_ortho]
  refine ⟨fun h G hFG haG ↦ ofFilters_compat.1 hFG aᶜ h
    (by rw [InvolutiveCompl.compl_compl]; exact haG), fun h ↦ ?_⟩
  by_contra haF
  have ha : a ≠ ⊥ := fun h0 ↦ haF (by rw [h0, InvolutiveCompl.compl_bot]; exact F.1.top_mem)
  refine h (principal ha) (ofFilters_compat.2 fun c hc hac ↦ haF (F.1.mem_of_le ?_ hc))
    ((mem_principal ha).2 le_rfl)
  exact InvolutiveCompl.le_compl_comm.mp ((mem_principal ha).1 hac)

variable {box : InfTopHom L L}

/-- The canonical frame is R-regular: a possibility compatible with one according to which `G`
might obtain is given by the filter generated by `◇` of `G` ([holliday-mandelkern-2024] proof of
Theorem 4.37). -/
theorem isRRegular_ofFilters (hT : ∀ a, box a ≤ a) : IsRRegular (ofFilters L) (access box) := by
  refine (isRRegular_iff _ _).2 fun F G' G hFG' hG'G ↦ ?_
  have key : ∀ c ∈ F.1, cᶜ ∉ upMap (diamondHom box) (OrderHomClass.mono _) G.1 :=
      fun c hc hcD ↦ by
    obtain ⟨a, haG, hac⟩ := mem_upMap.1 hcD
    have hbox : box aᶜ ∈ F.1 := F.1.mem_of_le (by
      simpa only [diamondHom_apply, InvolutiveCompl.compl_compl] using
        InvolutiveCompl.le_compl_comm.mp hac) hc
    exact ofFilters_compat.1 hG'G aᶜ (mem_access.1 hFG' aᶜ hbox)
      (by rwa [InvolutiveCompl.compl_compl])
  refine ⟨⟨upMap (diamondHom box) (OrderHomClass.mono _) G.1, fun h ↦ key ⊤ F.1.top_mem ?_⟩,
    ofFilters_compat.2 key, fun H hDH ↦ ⟨nec hT H, access_nec hT H, ofFilters_compat.2
      fun d hd hdG ↦ ofFilters_compat.1 hDH (diamondHom box dᶜ)
        ((mem_upMap (hf := OrderHomClass.mono _)).2 ⟨dᶜ, hdG, le_rfl⟩) ?_⟩⟩
  · rwa [InvolutiveCompl.compl_top]
  · simpa only [diamondHom_apply, InvolutiveCompl.compl_compl] using mem_nec.1 hd

/-- The canonical frame satisfies Knowability: everything accessible from the filter generated by
`□` of `F` refines `F`, and the filter is proper by Wittgenstein's Law
([holliday-mandelkern-2024] proof of Theorem 4.37). -/
theorem isKnowable_ofFilters (hE : IsEpistemic box) : IsKnowable (ofFilters L) (access box) := by
  refine ⟨fun F ↦ ⟨⟨upMap box (OrderHomClass.mono _) F.1, fun h ↦ ?_⟩, fun H hGH ↦ ?_⟩⟩
  · obtain ⟨a, haF, ha⟩ := mem_upMap.1 h
    rw [hE.wittgensteinLaw.eq_bot_of_box_eq_bot (le_bot_iff.mp ha)] at haF
    exact F.2 haF
  · exact (ofFilters L).mem_ofObject_ortho.2 fun I hHI ↦ ofFilters_compat.2 fun c hc hcI ↦
      ofFilters_compat.1 hHI c (mem_access.1 hGH c
        ((mem_upMap (hf := OrderHomClass.mono box)).2 ⟨c, hc, le_rfl⟩)) hcI

/-- On the canonical frame of an epistemic ortholattice, `filterEmbed` commutes with `□`
([holliday-mandelkern-2024] proof of Theorem 4.37). -/
theorem filterEmbed_box [IsRRegular (ofFilters L) (access box)] (hT : ∀ a, box a ≤ a)
    (a : L) : filterEmbed (box a) = (ofFilters L).necHom (access box) (filterEmbed a) :=
  SetLike.coe_injective (core_setOf_mem hT a).symm

end Compatibility

/-! ### Completeness -/

namespace ModalFormula

open Compatibility

variable {Var : Type u} {φ ψ : ModalFormula Var}

theorem eval_filterEmbed {box : InfTopHom L L} [IsRRegular (ofFilters L) (access box)]
    (hT : ∀ a, box a ≤ a) (v : Var → L) (φ : ModalFormula Var) :
    eval ((ofFilters L).necHom (access box)) (fun p ↦ filterEmbed (v p)) φ =
      filterEmbed (eval box v φ) := by
  induction φ with
  | top => exact filterEmbed_top.symm
  | var p => rfl
  | neg φ ih => rw [eval, eval, ih, filterEmbed_compl]
  | and φ ψ ihφ ihψ => rw [eval, eval, ihφ, ihψ, filterEmbed_inf]
  | box φ ih => rw [eval, eval, ih, filterEmbed_box hT]

/-- Consequence over epistemic compatibility frames implies derivability in EO
([holliday-mandelkern-2024] Theorem 4.37). -/
theorem frame_complete (h : FrameConsequence φ ψ) : EDerivable φ ψ := by
  refine complete fun {L} _ _ _ _ box hE v ↦ ?_
  have := isRRegular_ofFilters hE.apply_le
  have := isRefl_access hE.apply_le
  have := isKnowable_ofFilters hE
  have hframe := frameConsequence_iff_eval.mp h (ofFilters L) (access box)
    fun p ↦ filterEmbed (v p)
  rw [eval_filterEmbed hE.apply_le, eval_filterEmbed hE.apply_le] at hframe
  exact filterEmbed_le_filterEmbed.mp hframe

/-- EO is sound and complete for epistemic compatibility frames ([holliday-mandelkern-2024]
Theorem 4.37). -/
theorem derivable_iff_frameConsequence :
    EDerivable φ ψ ↔ FrameConsequence φ ψ :=
  ⟨frame_sound, frame_complete⟩

end ModalFormula

end Orthologic
