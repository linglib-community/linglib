module

public import Linglib.Core.Data.Finset.Update
public import Linglib.Semantics.Dynamic.DRT.Semantics
public import Linglib.Semantics.Dynamic.RegisterStructure

/-!
# DRSs on total assignments

On total assignments `V → M`, an assignment `g` extends `f` on a universe `U` when the two agree
off `U`, written `f[U]g`, and an assignment verifies an atom when it realizes it in `M`. This is
the interpretation `Interpretation.assignment M`. A referent that a sub-DRS declares again takes
a new value.

The relation a DRS denotes is the box over its universe testing its conditions
(`DRS.eval_assignment_eq_box`). Whether an assignment verifies a DRS depends only on its values
at the free referents (`DRS.dependsOn_verifiers_assignment`), alphabetic variants are verified by
the same assignments up to renaming (`DRS.mem_verifiers_assignment_map`), and a merge `K ⊕ K'`
denotes the composite of `K` and `K'` when no referent of the universe of `K'` is free in the
conditions of `K` (`DRS.eval_assignment_merge`).

## References

* [muskens-1996]
* [groenendijk-stokhof-1991]
-/

@[expose] public section

open FirstOrder FirstOrder.Language Function
open DynamicSemantics (Update)
open DynamicSemantics.Update (box mem_box_iff)
open SetRel

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} [DecidableEq V] (M : Type x) [L.Structure M]

/-- The interpretation of DRSs in the total assignments into a model: `f[U]g` when `f` and `g`
agree off `U`, and an atom is verified when it is realized. -/
def Interpretation.assignment : Interpretation L V (V → M) where
  extend U := {(f, g) | ∀ x ∉ U, g x = f x}
  atom a := {g | a.Realize g}
  eq x y := {g | g x = g y}
  extend_empty := by
    ext ⟨f, g⟩
    exact ⟨fun h ↦ (funext fun x ↦ h x (Finset.notMem_empty x)).symm, fun h _ _ ↦ h ▸ rfl⟩
  extend_union U U' := by
    ext ⟨f, g⟩
    constructor
    · intro h
      refine ⟨fun x ↦ if x ∈ U' then f x else g x, fun x hx ↦ ?_, fun x hx ↦ by simp [hx]⟩
      by_cases hx' : x ∈ U'
      · simp [hx']
      · simpa [hx'] using h x fun hmem ↦ (Finset.mem_union.1 hmem).elim hx hx'
    · rintro ⟨h, h₁, h₂⟩ x hx
      rw [Finset.mem_union, not_or] at hx
      exact (h₂ x hx.2).trans (h₁ x hx.1)

variable {M} {K : DRS L V} {f g : V → M} {U : Finset V}

theorem Interpretation.mem_extend_assignment :
    f ~[(Interpretation.assignment (L := L) M).extend U] g ↔ ∀ x ∉ U, g x = f x := Iff.rfl

@[simp] theorem Condition.mem_verifiers_assignment_atom (a : L.Atom V) :
    g ⊨[.assignment M] Condition.atom a ↔ a.Realize g := by
  rw [Condition.verifiers_atom]
  rfl

@[simp] theorem Condition.mem_verifiers_assignment_eq (x y : V) :
    g ⊨[.assignment M] (Condition.eq x y : Condition L V) ↔ g x = g y := by
  rw [Condition.verifiers_eq]
  rfl

theorem DRS.mem_eval_assignment :
    f ~[K.eval (.assignment M)] g ↔ (∀ x ∉ K.referents, g x = f x) ∧ g ⊨[.assignment M] K :=
  DRS.mem_eval_iff

theorem DRS.mem_dom_eval_assignment :
    f ∈ (K.eval (.assignment M)).dom ↔
      ∃ g, (∀ x ∉ K.referents, g x = f x) ∧ g ⊨[.assignment M] K := by
  simp only [mem_dom, DRS.mem_eval_assignment]

theorem Condition.mem_verifiers_assignment_imp {a c : DRS L V} :
    f ⊨[.assignment M] Condition.imp a c ↔
      ∀ g, (∀ x ∉ a.referents, g x = f x) → g ⊨[.assignment M] a →
        g ∈ (c.eval (.assignment M)).dom := by
  simp only [Condition.mem_verifiers_imp, DRS.mem_eval_assignment, and_imp, mem_dom]

/-- The relation a DRS denotes on assignments is the box over its universe that tests its
conditions. -/
theorem DRS.eval_assignment_eq_box (K : DRS L V) :
    K.eval (.assignment M) = box K.referents (K.verifiers (.assignment M)) := by
  ext ⟨f, g⟩
  exact DRS.mem_eval_assignment.trans mem_box_iff.symm

/-! ### Alphabetic variants -/

section Map

variable {W : Type*} [DecidableEq W]

omit [DecidableEq V] in
private theorem forall_notMem_image_iff (e : V ≃ W) (U : Finset V) (f g : W → M) :
    (∀ y ∉ U.image e, g y = f y) ↔ ∀ x ∉ U, (g ∘ e) x = (f ∘ e) x := by
  simp only [Function.comp_apply]
  refine ⟨fun h x hx => h (e x) (by simpa using hx), fun h y hy => ?_⟩
  have hx : e.symm y ∉ U := fun hm => hy (by simpa using Finset.mem_image_of_mem e hm)
  simpa using h (e.symm y) hx

private theorem DRS.mem_verifiers_assignment_map_of_forall (e : V ≃ W) (K : DRS L V)
    (g : W → M)
    (ih : ∀ c ∈ K.conditions, ∀ u : W → M,
      u ⊨[.assignment M] c.map e ↔ (u ∘ e) ⊨[.assignment M] c) :
    g ⊨[.assignment M] K.map e ↔ (g ∘ e) ⊨[.assignment M] K := by
  simp only [DRS.mem_verifiers_iff, DRS.conditions_map, List.forall_mem_map]
  exact forall_congr' fun c => imp_congr_right fun hc => ih c hc g

private theorem DRS.mem_eval_assignment_map_of_forall (e : V ≃ W) (K : DRS L V)
    (f g : W → M)
    (ih : ∀ c ∈ K.conditions, ∀ u : W → M,
      u ⊨[.assignment M] c.map e ↔ (u ∘ e) ⊨[.assignment M] c) :
    f ~[(K.map e).eval (.assignment M)] g ↔ (f ∘ e) ~[K.eval (.assignment M)] (g ∘ e) := by
  rw [DRS.mem_eval_assignment, DRS.mem_eval_assignment, DRS.referents_map]
  exact and_congr (forall_notMem_image_iff e _ f g)
    (DRS.mem_verifiers_assignment_map_of_forall e K g ih)

private theorem DRS.mem_dom_eval_assignment_map_of_forall (e : V ≃ W) (K : DRS L V)
    (f : W → M)
    (ih : ∀ c ∈ K.conditions, ∀ u : W → M,
      u ⊨[.assignment M] c.map e ↔ (u ∘ e) ⊨[.assignment M] c) :
    f ∈ ((K.map e).eval (.assignment M)).dom ↔ f ∘ e ∈ (K.eval (.assignment M)).dom := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g ∘ e, (DRS.mem_eval_assignment_map_of_forall e K f g ih).mp hg⟩
  · rintro ⟨g, hg⟩
    refine ⟨g ∘ e.symm, (DRS.mem_eval_assignment_map_of_forall e K f _ ih).mpr ?_⟩
    rwa [show (g ∘ e.symm) ∘ e = g from funext fun x ↦ by simp]

/-- An assignment verifies a renamed condition iff its pullback verifies the condition. -/
theorem Condition.mem_verifiers_assignment_map (e : V ≃ W) (c : Condition L V) :
    ∀ f : W → M, f ⊨[.assignment M] c.map e ↔ (f ∘ e) ⊨[.assignment M] c := by
  induction c with
  | atom a =>
    intro f
    simp only [Condition.map, Condition.mem_verifiers_assignment_atom]
    exact Iff.rfl
  | eq a b =>
    intro f
    simp only [Condition.map, Condition.mem_verifiers_assignment_eq]
    exact Iff.rfl
  | neg K ih =>
    intro f
    simp only [Condition.map, Condition.verifiers_neg, Set.mem_compl_iff]
    exact not_congr (DRS.mem_dom_eval_assignment_map_of_forall e K f ih)
  | imp a c iha ihc =>
    intro f
    simp only [Condition.map, Condition.mem_verifiers_imp]
    constructor
    · intro h g hg
      have hge : (g ∘ e.symm) ∘ e = g := funext fun x ↦ by simp
      obtain ⟨u, hu⟩ := h (g ∘ e.symm)
        ((DRS.mem_eval_assignment_map_of_forall e a f _ iha).mpr (by rwa [hge]))
      have hdom := (DRS.mem_dom_eval_assignment_map_of_forall e c (g ∘ e.symm) ihc).mp ⟨u, hu⟩
      rw [hge] at hdom
      exact hdom
    · intro h g hg
      exact (DRS.mem_dom_eval_assignment_map_of_forall e c g ihc).mpr
        (h _ ((DRS.mem_eval_assignment_map_of_forall e a f g iha).mp hg))
  | dis l r ihl ihr =>
    intro f
    simp only [Condition.map, Condition.verifiers_dis, Set.mem_union]
    exact or_congr (DRS.mem_dom_eval_assignment_map_of_forall e l f ihl)
      (DRS.mem_dom_eval_assignment_map_of_forall e r f ihr)

/-- An assignment verifies an alphabetic variant of a DRS iff its pullback verifies the DRS. -/
theorem DRS.mem_verifiers_assignment_map (e : V ≃ W) (f : W → M) (K : DRS L V) :
    f ⊨[.assignment M] K.map e ↔ (f ∘ e) ⊨[.assignment M] K :=
  DRS.mem_verifiers_assignment_map_of_forall e K f fun c _ ↦
    c.mem_verifiers_assignment_map e

theorem DRS.mem_dom_eval_assignment_map (e : V ≃ W) (f : W → M) (K : DRS L V) :
    f ∈ ((K.map e).eval (.assignment M)).dom ↔ f ∘ e ∈ (K.eval (.assignment M)).dom :=
  DRS.mem_dom_eval_assignment_map_of_forall e K f fun c _ ↦
    c.mem_verifiers_assignment_map e

end Map

/-! ### Coincidence -/

private theorem exists_agree_iff {P : (V → M) → Prop} :
    (∃ g, (∀ x ∉ U, g x = f x) ∧ P g) ↔ ∃ y : U → M, P (updateFinset f U y) := by
  simp only [← mem_range_updateFinset_iff, Set.exists_range_iff]

private theorem forall_agree_iff {P : (V → M) → Prop} :
    (∀ g, (∀ x ∉ U, g x = f x) → P g) ↔ ∀ y : U → M, P (updateFinset f U y) := by
  simp only [← mem_range_updateFinset_iff, Set.forall_mem_range]

private theorem dependsOn_exists_agree {P : (V → M) → Prop} {S : Set V} (U : Finset V)
    (hP : DependsOn P S) :
    DependsOn (fun f : V → M ↦ ∃ g, (∀ x ∉ U, g x = f x) ∧ P g) (S \ ↑U) := fun _ _ h ↦ by
  simp only [exists_agree_iff]
  exact propext <| exists_congr fun y ↦ (hP.updateFinset y h).to_iff

private theorem dependsOn_forall_agree {P : (V → M) → Prop} {S : Set V} (U : Finset V)
    (hP : DependsOn P S) :
    DependsOn (fun f : V → M ↦ ∀ g, (∀ x ∉ U, g x = f x) → P g) (S \ ↑U) := fun _ _ h ↦ by
  simp only [forall_agree_iff]
  exact propext <| forall_congr' fun y ↦ (hP.updateFinset y h).to_iff

private theorem DRS.dependsOn_verifiers_assignment_of_forall {K : DRS L V}
    (ih : ∀ c ∈ K.conditions,
      DependsOn (fun f : V → M ↦ f ⊨[.assignment M] c) ↑c.freeVarFinset) :
    DependsOn (fun f : V → M ↦ f ⊨[.assignment M] K)
      ↑(Condition.freeVarFinsetL K.conditions) :=
  fun _ _ h ↦ propext <| by
    simp only [DRS.mem_verifiers_iff]
    exact forall₂_congr fun c hc ↦ (ih c hc fun i hi ↦ h i <| Finset.coe_subset.mpr
      (Condition.freeVarFinset_subset_freeVarFinsetL hc) hi).to_iff

/-- Whether an assignment verifies a condition depends only on its values at the free referents
of the condition. -/
theorem Condition.dependsOn_verifiers_assignment (c : Condition L V) :
    DependsOn (fun f : V → M ↦ f ⊨[.assignment M] c) ↑c.freeVarFinset := by
  induction c with
  | atom a =>
    refine fun f₁ f₂ h ↦ propext ?_
    simp only [Condition.mem_verifiers_assignment_atom, Atom.Realize]
    rw [show f₁ ∘ a.args = f₂ ∘ a.args from funext fun i ↦ h _ (by simp)]
  | eq a b =>
    refine fun f₁ f₂ h ↦ propext ?_
    simp only [Condition.mem_verifiers_assignment_eq]
    rw [h _ (by simp), h _ (by simp)]
  | neg K ih =>
    rw [Condition.freeVarFinset_neg, DRS.coe_freeVarFinset]
    refine fun f₁ f₂ h ↦ propext ?_
    simp only [Condition.verifiers_neg, Set.mem_compl_iff, DRS.mem_dom_eval_assignment]
    exact not_congr (dependsOn_exists_agree K.referents
      (DRS.dependsOn_verifiers_assignment_of_forall ih) h).to_iff
  | imp a c iha ihc =>
    rw [Condition.freeVarFinset_imp, Finset.coe_union, Finset.coe_sdiff, DRS.coe_freeVarFinset,
      DRS.coe_freeVarFinset, ← Set.union_sdiff_distrib]
    refine fun f₁ f₂ h ↦ propext ?_
    dsimp only
    rw [Condition.mem_verifiers_assignment_imp, Condition.mem_verifiers_assignment_imp]
    refine (dependsOn_forall_agree a.referents
      (P := fun g ↦ g ⊨[.assignment M] a → g ∈ (c.eval (.assignment M)).dom)
      (fun g₁ g₂ h' ↦ propext ?_) h).to_iff
    refine imp_congr
      (DRS.dependsOn_verifiers_assignment_of_forall iha fun i hi ↦ h' i (.inl hi)).to_iff ?_
    rw [DRS.mem_dom_eval_assignment, DRS.mem_dom_eval_assignment]
    exact (dependsOn_exists_agree c.referents
      (DRS.dependsOn_verifiers_assignment_of_forall ihc) fun i hi ↦ h' i (.inr hi)).to_iff
  | dis l r ihl ihr =>
    rw [Condition.freeVarFinset_dis, Finset.coe_union, DRS.coe_freeVarFinset,
      DRS.coe_freeVarFinset]
    refine fun f₁ f₂ h ↦ propext ?_
    simp only [Condition.verifiers_dis, Set.mem_union, DRS.mem_dom_eval_assignment]
    exact or_congr
      (dependsOn_exists_agree l.referents (DRS.dependsOn_verifiers_assignment_of_forall ihl)
        fun i hi ↦ h i (.inl hi)).to_iff
      (dependsOn_exists_agree r.referents (DRS.dependsOn_verifiers_assignment_of_forall ihr)
        fun i hi ↦ h i (.inr hi)).to_iff

/-- Whether an assignment verifies a DRS depends only on its values at the free referents of
the conditions. -/
theorem DRS.dependsOn_verifiers_assignment (K : DRS L V) :
    DependsOn (fun f : V → M ↦ f ⊨[.assignment M] K)
      ↑(Condition.freeVarFinsetL K.conditions) :=
  DRS.dependsOn_verifiers_assignment_of_forall fun c _ ↦ c.dependsOn_verifiers_assignment

/-- Whether an assignment has an extension verifying a DRS depends only on its values at the
free referents of the DRS. -/
theorem DRS.dependsOn_mem_dom_eval_assignment (K : DRS L V) :
    DependsOn (fun f : V → M ↦ f ∈ (K.eval (.assignment M)).dom) ↑K.freeVarFinset := by
  rw [DRS.coe_freeVarFinset]
  refine fun f₁ f₂ h ↦ propext ?_
  dsimp only
  rw [DRS.mem_dom_eval_assignment, DRS.mem_dom_eval_assignment]
  exact (dependsOn_exists_agree K.referents K.dependsOn_verifiers_assignment h).to_iff

/-- Every assignment has an extension verifying a proper DRS iff some assignment verifies it. -/
theorem DRS.mem_dom_eval_assignment_iff_of_isProper (hK : K.IsProper) (f : V → M) :
    f ∈ (K.eval (.assignment M)).dom ↔ ∃ g : V → M, g ⊨[.assignment M] K := by
  refine ⟨fun ⟨g, hg⟩ ↦ ⟨g, (DRS.mem_eval_assignment.mp hg).2⟩, fun ⟨g, hg⟩ ↦ ?_⟩
  have hdep := DRS.dependsOn_mem_dom_eval_assignment (M := M) K
  rw [show K.freeVarFinset = ∅ from hK, Finset.coe_empty] at hdep
  exact (hdep.empty g f).to_iff.mp ⟨g, DRS.mem_eval_assignment.mpr ⟨fun _ _ ↦ rfl, hg⟩⟩

/-! ### The Merging Lemma -/

/-- The Merging Lemma: a merge denotes the composite of its parts when no referent of the
universe of `K₂` is free in the conditions of `K₁`. -/
theorem DRS.eval_assignment_merge (K₁ K₂ : DRS L V)
    (hfresh : Disjoint K₂.referents (Condition.freeVarFinsetL K₁.conditions)) :
    (K₁.merge K₂).eval (.assignment M) = K₁.eval (.assignment M) ○ K₂.eval (.assignment M) :=
  DRS.eval_merge K₁ K₂ fun _ _ _ hst ↦ (K₁.dependsOn_verifiers_assignment fun y hy ↦
    (hst y fun hy₂ ↦ Finset.disjoint_left.1 hfresh hy₂ (Finset.mem_coe.1 hy)).symm).to_iff

end DRT
