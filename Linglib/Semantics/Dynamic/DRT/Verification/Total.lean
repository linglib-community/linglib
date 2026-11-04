module

public import Linglib.Core.Data.Finset.Update
public import Linglib.Semantics.Dynamic.DRT.Syntax

/-!
# Verification by total assignments

This file defines the verification of a DRS by total assignments. An assignment verifies a DRS
when it verifies each of its conditions, and a sub-DRS is entered by reassigning its universe, so
a referent declared twice takes a fresh value the second time. Verification [reads an assignment
only at the free referents](##DRT.dependsOn_verifiesConditionTotal), and [alphabetic variants
agree](##DRT.verifiesTotal_map).

## Main definitions

* `DRT.DRS.Extends`: the relation between assignments that differ at most on the universe of a DRS.
* `DRT.VerifiesTotal`, `DRT.VerifiesConditionTotal`: verification of DRSs and conditions.

## Implementation notes

The quantifier over assignments reduces to a quantifier over values for the universe
(`DRS.exists_extends_iff`), which is `Function.updateFinset`; mathlib's `DependsOn.updateFinset`
then gives coincidence.

## References

* [muskens-1996]
-/

@[expose] public section

open FirstOrder FirstOrder.Language Function

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {M : Type x}

/-! ### Assignments that differ on a universe -/

namespace DRS

/-- `K.Extends f g` says `f` and `g` differ at most in their values for the universe of `K`. This
is Muskens's `a[x₁, …, xₙ]a'` (p. 148), the total rendering of the partial embeddings' "`f ⊆ g`
and `Dom g = Dom f ∪ U_K`"; on total assignments it is symmetric. -/
def Extends (K : DRS L V) (f g : V → M) : Prop := ∀ x ∉ K.referents, g x = f x

variable {W : Type*} {K : DRS L V} {f g : V → M} {P : (V → M) → Prop} {S : Set V}

theorem Extends.refl (K : DRS L V) (f : V → M) : K.Extends f f := fun _ _ ↦ rfl

theorem Extends.symm (h : K.Extends f g) : K.Extends g f := fun x hx ↦ (h x hx).symm

theorem extends_map [DecidableEq W] (e : V ≃ W) (K : DRS L V) (f g : W → M) :
    (K.map e).Extends f g ↔ K.Extends (f ∘ e) (g ∘ e) := by
  simp only [Extends, referents_map, Function.comp_apply]
  refine ⟨fun h x hx => h (e x) (by simpa using hx), fun h y hy => ?_⟩
  have hx : e.symm y ∉ K.referents := fun hm =>
    hy (by simpa using Finset.mem_image_of_mem e hm)
  simpa using h (e.symm y) hx

theorem exists_extends_map [DecidableEq W] (e : V ≃ W) (K : DRS L V) (f : W → M)
    (P : (V → M) → Prop) :
    (∃ g, (K.map e).Extends f g ∧ P (g ∘ e)) ↔ ∃ g, K.Extends (f ∘ e) g ∧ P g := by
  simp only [extends_map]
  refine ⟨fun ⟨g, hg, hp⟩ => ⟨g ∘ e, hg, hp⟩, fun ⟨g, hg, hp⟩ => ⟨g ∘ e.symm, ?_⟩⟩
  have key : (g ∘ e.symm) ∘ e = g := by funext x; simp
  exact key.symm ▸ ⟨hg, hp⟩

theorem forall_extends_map [DecidableEq W] (e : V ≃ W) (K : DRS L V) (f : W → M)
    (P : (V → M) → Prop) :
    (∀ g, (K.map e).Extends f g → P (g ∘ e)) ↔ ∀ g, K.Extends (f ∘ e) g → P g := by
  simp only [extends_map]
  refine ⟨fun H g hg => ?_, fun H g hg => H (g ∘ e) hg⟩
  have key : (g ∘ e.symm) ∘ e = g := by funext x; simp
  exact key ▸ H (g ∘ e.symm) (key.symm ▸ hg)

variable [DecidableEq V]

theorem extends_iff_mem_range : K.Extends f g ↔ g ∈ Set.range (updateFinset f K.referents) :=
  mem_range_updateFinset_iff.symm

/-- Some assignment differing from `f` on the universe satisfies `P` iff some values for the
universe do. -/
theorem exists_extends_iff :
    (∃ g, K.Extends f g ∧ P g) ↔ ∃ y : K.referents → M, P (updateFinset f K.referents y) := by
  simp only [extends_iff_mem_range, Set.exists_range_iff]

theorem forall_extends_iff :
    (∀ g, K.Extends f g → P g) ↔ ∀ y : K.referents → M, P (updateFinset f K.referents y) := by
  simp only [extends_iff_mem_range, Set.forall_mem_range]

theorem dependsOn_exists_extends (K : DRS L V) (hP : DependsOn P S) :
    DependsOn (fun f : V → M ↦ ∃ g, K.Extends f g ∧ P g) (S \ ↑K.referents) := fun _ _ h ↦ by
  simp only [exists_extends_iff]
  exact propext <| exists_congr fun y ↦ (hP.updateFinset y h).to_iff

theorem dependsOn_forall_extends (K : DRS L V) (hP : DependsOn P S) :
    DependsOn (fun f : V → M ↦ ∀ g, K.Extends f g → P g) (S \ ↑K.referents) := fun _ _ h ↦ by
  simp only [forall_extends_iff]
  exact propext <| forall_congr' fun y ↦ (hP.updateFinset y h).to_iff

end DRS

variable [L.Structure M]

/-! ### Verification -/

mutual
/-- `VerifiesTotal f K` says the total assignment `f` verifies every condition of `K`. -/
def VerifiesTotal : (V → M) → DRS L V → Prop
  | f, ⟨_, cs⟩ => VerifiesAllTotal f cs
/-- `VerifiesConditionTotal f c` says the total assignment `f` verifies the DRS-condition `c`;
a sub-DRS is entered by existentially (re)assigning along its extension relation. -/
def VerifiesConditionTotal : (V → M) → Condition L V → Prop
  | f, .atom a => a.Realize f
  | f, .eq a b => f a = f b
  | f, .neg K => ¬ ∃ g, K.Extends f g ∧ VerifiesTotal g K
  | f, .imp a c => ∀ g, a.Extends f g → VerifiesTotal g a →
      ∃ h, c.Extends g h ∧ VerifiesTotal h c
  | f, .dis l r =>
      (∃ g, l.Extends f g ∧ VerifiesTotal g l) ∨ (∃ g, r.Extends f g ∧ VerifiesTotal g r)
/-- `VerifiesAllTotal f cs` says `f` verifies every condition of `cs`. -/
def VerifiesAllTotal : (V → M) → List (Condition L V) → Prop
  | _, [] => True
  | f, c :: cs => VerifiesConditionTotal f c ∧ VerifiesAllTotal f cs
end

variable {f' : V → M}

theorem verifiesAllTotal_iff {cs : List (Condition L V)} :
    VerifiesAllTotal f' cs ↔ ∀ c ∈ cs, VerifiesConditionTotal f' c := by
  induction cs with
  | nil => simp [VerifiesAllTotal]
  | cons c cs ih => simp [VerifiesAllTotal, ih]

@[simp] theorem verifiesTotal_mk (U : Finset V) (conds : List (Condition L V)) :
    VerifiesTotal f' (.mk U conds) ↔ ∀ c ∈ conds, VerifiesConditionTotal f' c :=
  verifiesAllTotal_iff

theorem verifiesTotal_iff {K : DRS L V} :
    VerifiesTotal f' K ↔ ∀ c ∈ K.conditions, VerifiesConditionTotal f' c := by
  cases K; exact verifiesAllTotal_iff

@[simp] theorem verifiesTotal_empty : VerifiesTotal f' (.empty : DRS L V) := by
  simp [DRS.empty]

@[simp] theorem verifiesTotal_merge [DecidableEq V] (K₁ K₂ : DRS L V) :
    VerifiesTotal f' (K₁.merge K₂) ↔ VerifiesTotal f' K₁ ∧ VerifiesTotal f' K₂ := by
  simp only [verifiesTotal_iff, DRS.conditions_merge, List.forall_mem_append]

@[simp] theorem verifiesTotal_atom (a : L.Atom V) :
    VerifiesConditionTotal f' (.atom a) ↔ a.Realize f' := .rfl

@[simp] theorem verifiesTotal_eq (a b : V) :
    VerifiesConditionTotal f' (.eq a b : Condition L V) ↔ f' a = f' b := Iff.rfl

@[simp] theorem verifiesTotal_neg (K : DRS L V) :
    VerifiesConditionTotal f' (.neg K) ↔ ¬ ∃ g, K.Extends f' g ∧ VerifiesTotal g K := Iff.rfl

@[simp] theorem verifiesTotal_imp (a c : DRS L V) :
    VerifiesConditionTotal f' (.imp a c) ↔
      ∀ g, a.Extends f' g → VerifiesTotal g a →
        ∃ h, c.Extends g h ∧ VerifiesTotal h c := Iff.rfl

@[simp] theorem verifiesTotal_dis (l r : DRS L V) :
    VerifiesConditionTotal f' (.dis l r) ↔
      (∃ g, l.Extends f' g ∧ VerifiesTotal g l) ∨
        (∃ g, r.Extends f' g ∧ VerifiesTotal g r) := Iff.rfl

theorem verifiesTotal_perm {U : Finset V} {cs ds : List (Condition L V)} (h : cs.Perm ds) :
    VerifiesTotal f' (.mk U cs) ↔ VerifiesTotal f' (.mk U ds) := by
  simp only [verifiesTotal_mk, h.mem_iff]

/-! ### Alphabetic variants -/

section Map

variable {W : Type*} [DecidableEq W]

private theorem verifiesTotal_map_all (e : V ≃ W) (K : DRS L V) (g : W → M)
    (ih : ∀ c ∈ K.conditions, ∀ u : W → M,
      VerifiesConditionTotal u (c.map e) ↔ VerifiesConditionTotal (u ∘ e) c) :
    VerifiesTotal g (K.map e) ↔ VerifiesTotal (g ∘ e) K := by
  simp only [verifiesTotal_iff, DRS.conditions_map, List.forall_mem_map]
  exact forall_congr' fun c => imp_congr_right fun hc => ih c hc g

private theorem exists_extends_verifiesTotal_map_aux (e : V ≃ W) (K : DRS L V) (f : W → M)
    (ih : ∀ c ∈ K.conditions, ∀ u : W → M,
      VerifiesConditionTotal u (c.map e) ↔ VerifiesConditionTotal (u ∘ e) c) :
    (∃ g, (K.map e).Extends f g ∧ VerifiesTotal g (K.map e)) ↔
      ∃ g, K.Extends (f ∘ e) g ∧ VerifiesTotal g K :=
  (exists_congr fun g => and_congr_right fun _ => verifiesTotal_map_all e K g ih).trans
    (DRS.exists_extends_map e K f (VerifiesTotal · K))

theorem verifiesTotal_map_condition (e : V ≃ W) (f : W → M) (c : Condition L V) :
    VerifiesConditionTotal f (c.map e) ↔ VerifiesConditionTotal (f ∘ e) c := by
  induction c generalizing f with
  | atom a => simp [Condition.map]
  | eq a b => simp [Condition.map]
  | neg K ih =>
    simp only [Condition.map, verifiesTotal_neg]
    exact not_congr (exists_extends_verifiesTotal_map_aux e K f ih)
  | imp a c iha ihc =>
    simp only [Condition.map, verifiesTotal_imp]
    refine Iff.trans (forall_congr' fun g => imp_congr_right fun _ => imp_congr
      (verifiesTotal_map_all e a g iha) (exists_extends_verifiesTotal_map_aux e c g ihc)) ?_
    exact DRS.forall_extends_map e a f
      (fun u => VerifiesTotal u a → ∃ h', c.Extends u h' ∧ VerifiesTotal h' c)
  | dis l r ihl ihr =>
    simp only [Condition.map, verifiesTotal_dis]
    exact or_congr (exists_extends_verifiesTotal_map_aux e l f ihl)
      (exists_extends_verifiesTotal_map_aux e r f ihr)

/-- `f` verifies `K.map e` iff `f ∘ e` verifies `K`, so alphabetic variants have the same
semantics. -/
theorem verifiesTotal_map (e : V ≃ W) (f : W → M) (K : DRS L V) :
    VerifiesTotal f (K.map e) ↔ VerifiesTotal (f ∘ e) K :=
  verifiesTotal_map_all e K f (fun c _ u => verifiesTotal_map_condition e u c)

theorem exists_extends_verifiesTotal_map (e : V ≃ W) (f : W → M) (K : DRS L V) :
    (∃ g, (K.map e).Extends f g ∧ VerifiesTotal g (K.map e)) ↔
      ∃ g, K.Extends (f ∘ e) g ∧ VerifiesTotal g K :=
  (exists_congr fun g => and_congr_right fun _ => verifiesTotal_map e g K).trans
    (DRS.exists_extends_map e K f (VerifiesTotal · K))

end Map

/-! ### Coincidence -/

section Coincidence

variable [DecidableEq V]

private theorem dependsOn_verifiesTotal_of_forall {K : DRS L V}
    (ih : ∀ c ∈ K.conditions, DependsOn (VerifiesConditionTotal (M := M) · c) ↑c.freeVarFinset) :
    DependsOn (VerifiesTotal (M := M) · K) ↑(Condition.freeVarFinsetL K.conditions) :=
  fun _ _ h ↦ propext <| by
    simp only [verifiesTotal_iff]
    exact forall₂_congr fun c hc ↦ (ih c hc fun i hi ↦ h i <| Finset.coe_subset.mpr
      (Condition.freeVarFinset_subset_freeVarFinsetL hc) hi).to_iff

/-- Verification of a condition reads an assignment only at the condition's free referents
(Def. 1.4.2). -/
theorem dependsOn_verifiesConditionTotal (c : Condition L V) :
    DependsOn (VerifiesConditionTotal (M := M) · c) ↑c.freeVarFinset := by
  induction c with
  | atom a =>
    refine fun f₁ f₂ h ↦ propext ?_
    simp only [verifiesTotal_atom, Atom.Realize]
    rw [show f₁ ∘ a.args = f₂ ∘ a.args from funext fun i ↦ h _ (by simp)]
  | eq a b =>
    refine fun f₁ f₂ h ↦ propext ?_
    simp only [verifiesTotal_eq]
    rw [h _ (by simp), h _ (by simp)]
  | neg K ih =>
    rw [Condition.freeVarFinset_neg, DRS.coe_freeVarFinset]
    exact fun _ _ h ↦ propext <| not_congr
      (K.dependsOn_exists_extends (dependsOn_verifiesTotal_of_forall ih) h).to_iff
  | imp a c iha ihc =>
    rw [Condition.freeVarFinset_imp, Finset.coe_union, Finset.coe_sdiff, DRS.coe_freeVarFinset,
      DRS.coe_freeVarFinset, ← Set.union_sdiff_distrib]
    refine a.dependsOn_forall_extends (P := fun g ↦ VerifiesTotal g a →
      ∃ h, c.Extends g h ∧ VerifiesTotal h c) fun _ _ h ↦ propext ?_
    exact imp_congr
      (dependsOn_verifiesTotal_of_forall iha fun i hi ↦ h i (.inl hi)).to_iff
      (c.dependsOn_exists_extends (dependsOn_verifiesTotal_of_forall ihc)
        fun i hi ↦ h i (.inr hi)).to_iff
  | dis l r ihl ihr =>
    rw [Condition.freeVarFinset_dis, Finset.coe_union, DRS.coe_freeVarFinset,
      DRS.coe_freeVarFinset]
    exact fun _ _ h ↦ propext <| or_congr
      (l.dependsOn_exists_extends (dependsOn_verifiesTotal_of_forall ihl)
        fun i hi ↦ h i (.inl hi)).to_iff
      (r.dependsOn_exists_extends (dependsOn_verifiesTotal_of_forall ihr)
        fun i hi ↦ h i (.inr hi)).to_iff

theorem dependsOn_verifiesTotal (K : DRS L V) :
    DependsOn (VerifiesTotal (M := M) · K) ↑(Condition.freeVarFinsetL K.conditions) :=
  dependsOn_verifiesTotal_of_forall fun c _ ↦ dependsOn_verifiesConditionTotal c

/-- "Some assignment differing on the universe verifies `K`" reads the input only at `K`'s free
referents. -/
theorem dependsOn_exists_extends_verifiesTotal (K : DRS L V) :
    DependsOn (fun f : V → M ↦ ∃ g, K.Extends f g ∧ VerifiesTotal g K) ↑K.freeVarFinset := by
  rw [DRS.coe_freeVarFinset]
  exact K.dependsOn_exists_extends (dependsOn_verifiesTotal K)

/-- A proper DRS is verified by some extension of any input iff some assignment verifies it. -/
theorem exists_extends_verifiesTotal_iff_of_isProper {K : DRS L V} (hK : K.IsProper)
    (f : V → M) : (∃ g, K.Extends f g ∧ VerifiesTotal g K) ↔ ∃ g : V → M, VerifiesTotal g K := by
  refine ⟨fun ⟨g, _, hg⟩ ↦ ⟨g, hg⟩, fun ⟨g, hg⟩ ↦ ?_⟩
  have hdep := dependsOn_exists_extends_verifiesTotal (M := M) K
  rw [show K.freeVarFinset = ∅ from hK, Finset.coe_empty] at hdep
  exact (hdep.empty g f).to_iff.mp ⟨g, .refl K g, hg⟩

end Coincidence

end DRT
