module

public import Linglib.Semantics.Dynamic.DRS.Basic
public import Linglib.Semantics.Dynamic.DRS.Dynamics
public import Linglib.Semantics.Dynamic.Transition

/-!
# DRS semantics at a base

This file defines Kamp, van Genabith and Reyle's semantics of DRSs, in which an output embedding
extends its input: `DRS.toRelAt X K f g` holds when `g` agrees with `f` on the base `X` and
verifies the conditions of `K` at `X ∪ U`. Values of established referents persist, which is
why we call it the persistence semantics, unlike the box relation `DRS.toRel` of
`DRS/Dynamics.lean`, which reassigns a re-declared referent. Over an intensional model it is the
context change potential of a DRS, and a proper DRS expresses the information state this produces
from the empty state.

## Main statements

* `DRS.toRelAt_merge`: the Merging Lemma, under a weaker hypothesis than the box relation's: the
  second universe may re-declare referents of the first DRS but not capture its sub-DRSs'.
* `DRS.trueRel_iff_toRelAt`: on reuse-free DRSs the two semantics have the same truth conditions.
* `DRS.state_merge`: the context change potential of a DRS takes the state of a proper context
  DRS to the state of their merge.

## Implementation notes

An embedding with domain `X` is a total assignment read only at `X`. An intensional model, with
constant domain and world-relative relations, is a family `interp : W → L.Structure M`.

## References

* [kamp-vangenabith-reyle-2011]
* [kamp-reyle-1993]
* [muskens-1996]
-/

@[expose] public section

open FirstOrder FirstOrder.Language
open DynamicSemantics

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {M : Type x} [DecidableEq V]

section Semantics

variable [L.Structure M]

/-! ### The persistence semantics -/

mutual
/-- The persistence semantics of a DRS at the base `X` (Def. 19(i)): the output agrees with the
input on `X` and verifies the conditions at `X ∪ U`. -/
def DRS.toRelAt (X : Finset V) : DRS L V → (V → M) → (V → M) → Prop
  | .mk U conds => fun f g => Set.EqOn g f ↑X ∧ Condition.holdsAllAt (X ∪ U) conds g
/-- A condition holds at a base under an assignment (Def. 19(ii)–(vii)), its sub-DRSs entered
at the base. -/
def Condition.holdsAt (X : Finset V) : Condition L V → (V → M) → Prop
  | .atom a => a.Realize
  | .eq u v => fun g => g u = g v
  | .neg K => fun g => ¬ ∃ g', DRS.toRelAt X K g g'
  | .imp a c => fun g => ∀ g', DRS.toRelAt X a g g' →
      ∃ g'', DRS.toRelAt (X ∪ a.referents) c g' g''
  | .dis l r => fun g => ∃ g', DRS.toRelAt X l g g' ∨ DRS.toRelAt X r g g'
/-- Every condition of a list holds at the base. -/
def Condition.holdsAllAt (X : Finset V) : List (Condition L V) → (V → M) → Prop
  | [] => fun _ => True
  | c :: cs => fun g => Condition.holdsAt X c g ∧ Condition.holdsAllAt X cs g
end

@[simp] theorem DRS.toRelAt_mk (X U : Finset V) (conds : List (Condition L V))
    (f g : V → M) :
    DRS.toRelAt X (.mk U conds) f g ↔
      Set.EqOn g f ↑X ∧ Condition.holdsAllAt (X ∪ U) conds g := Iff.rfl

@[simp] theorem Condition.holdsAt_atom (X : Finset V) (a : L.Atom V) (g : V → M) :
    (Condition.atom a).holdsAt X g ↔ a.Realize g := .rfl

@[simp] theorem Condition.holdsAt_eq (X : Finset V) (u v : V) (g : V → M) :
    (Condition.eq u v : Condition L V).holdsAt X g ↔ g u = g v := Iff.rfl

@[simp] theorem Condition.holdsAt_neg (X : Finset V) (K : DRS L V) (g : V → M) :
    (Condition.neg K).holdsAt X g ↔ ¬ ∃ g', DRS.toRelAt X K g g' := Iff.rfl

@[simp] theorem Condition.holdsAt_imp (X : Finset V) (a c : DRS L V) (g : V → M) :
    (Condition.imp a c).holdsAt X g ↔
      ∀ g', DRS.toRelAt X a g g' → ∃ g'', DRS.toRelAt (X ∪ a.referents) c g' g'' := Iff.rfl

@[simp] theorem Condition.holdsAt_dis (X : Finset V) (l r : DRS L V) (g : V → M) :
    (Condition.dis l r).holdsAt X g ↔
      ∃ g', DRS.toRelAt X l g g' ∨ DRS.toRelAt X r g g' := Iff.rfl

@[simp] theorem Condition.holdsAllAt_nil (X : Finset V) (g : V → M) :
    Condition.holdsAllAt X ([] : List (Condition L V)) g := trivial

@[simp] theorem Condition.holdsAllAt_cons (X : Finset V) (c : Condition L V)
    (cs : List (Condition L V)) (g : V → M) :
    Condition.holdsAllAt X (c :: cs) g ↔
      Condition.holdsAt X c g ∧ Condition.holdsAllAt X cs g := Iff.rfl

@[simp] theorem Condition.holdsAllAt_append (X : Finset V)
    (cs ds : List (Condition L V)) (g : V → M) :
    Condition.holdsAllAt X (cs ++ ds) g ↔
      Condition.holdsAllAt X cs g ∧ Condition.holdsAllAt X ds g := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih, and_assoc]

/-! ### Read and write support -/

theorem DRS.toRelAt_congr_left (X : Finset V) (K : DRS L V) {f f' g : V → M}
    (h : Set.EqOn f f' ↑X) : DRS.toRelAt X K f g ↔ DRS.toRelAt X K f' g := by
  obtain ⟨U, conds⟩ := K
  simp only [DRS.toRelAt_mk]
  exact and_congr_left fun _ => ⟨fun he => he.trans h, fun he => he.trans h.symm⟩

theorem Condition.holdsAt_congr {X : Finset V} (c : Condition L V)
    (hfv : c.freeVarFinset ⊆ X) {g g' : V → M} (hgg' : Set.EqOn g g' ↑X) :
    Condition.holdsAt X c g ↔ Condition.holdsAt X c g' := by
  match c with
  | .atom a =>
    simp only [Condition.holdsAt_atom, Atom.Realize]
    rw [show g ∘ a.args = g' ∘ a.args from
      funext fun i => hgg' (Finset.mem_coe.mpr (hfv (by simp)))]
  | .eq u v =>
    simp only [Condition.holdsAt_eq]
    rw [hgg' (Finset.mem_coe.mpr (hfv (by simp))), hgg' (Finset.mem_coe.mpr (hfv (by simp)))]
  | .neg K => exact not_congr (exists_congr fun _ => DRS.toRelAt_congr_left X K hgg')
  | .imp a c =>
    exact forall_congr' fun _ => imp_congr (DRS.toRelAt_congr_left X a hgg') Iff.rfl
  | .dis l r =>
    exact exists_congr fun _ =>
      or_congr (DRS.toRelAt_congr_left X l hgg') (DRS.toRelAt_congr_left X r hgg')

theorem Condition.holdsAllAt_congr {X : Finset V} (cs : List (Condition L V))
    (hfv : Condition.freeVarFinsetL cs ⊆ X) {g g' : V → M} (hgg' : Set.EqOn g g' ↑X) :
    Condition.holdsAllAt X cs g ↔ Condition.holdsAllAt X cs g' := by
  induction cs with
  | nil => exact Iff.rfl
  | cons c cs ih =>
    rw [Condition.freeVarFinsetL_cons, Finset.union_subset_iff] at hfv
    exact and_congr (Condition.holdsAt_congr c hfv.1 hgg') (ih hfv.2)

theorem DRS.toRelAt_congr_right {X : Finset V} (K : DRS L V) (hfv : K.freeVarFinset ⊆ X)
    {f g g' : V → M} (hgg' : Set.EqOn g g' ↑(X ∪ K.referents)) :
    DRS.toRelAt X K f g ↔ DRS.toRelAt X K f g' := by
  obtain ⟨U, conds⟩ := K
  have hX : Set.EqOn g g' ↑X := hgg'.mono (by simp)
  simp only [DRS.toRelAt_mk]
  exact and_congr ⟨fun he => hX.symm.trans he, fun he => hX.trans he⟩
    (Condition.holdsAllAt_congr conds (DRS.freeVarFinset_subset_iff.mp hfv) hgg')

theorem DRS.eqOn_piecewise_of_toRelAt {X Δ : Finset V} {K : DRS L V}
    (hΔ : Disjoint Δ (K.referents \ X)) {f g : V → M} (h : DRS.toRelAt X K f g) :
    Set.EqOn (Δ.piecewise f g) g ↑(X ∪ K.referents) := by
  obtain ⟨U, conds⟩ := K
  intro x hx
  by_cases hxΔ : x ∈ Δ
  · rw [Finset.piecewise_eq_of_mem _ _ _ hxΔ]
    refine (h.1 ?_).symm
    by_contra hxX
    refine Finset.disjoint_left.mp hΔ hxΔ (Finset.mem_sdiff.mpr ⟨?_, hxX⟩)
    exact (Finset.mem_union.mp hx).resolve_left hxX
  · exact Finset.piecewise_eq_of_notMem _ _ _ hxΔ

theorem DRS.exists_toRelAt_and_eqOn_iff {X Δ : Finset V} {K : DRS L V}
    (hΔ : Disjoint Δ (K.varFinset \ X)) (hfv : K.freeVarFinset ⊆ X) {f : V → M} :
    (∃ g, DRS.toRelAt X K f g ∧ Set.EqOn g f ↑Δ) ↔ ∃ g, DRS.toRelAt X K f g := by
  refine ⟨fun ⟨g, hg, _⟩ => ⟨g, hg⟩, fun ⟨g, hg⟩ => ⟨Δ.piecewise f g, ?_,
    fun _ hx => Finset.piecewise_eq_of_mem _ _ _ hx⟩⟩
  refine (DRS.toRelAt_congr_right K hfv (DRS.eqOn_piecewise_of_toRelAt ?_ hg).symm).mp hg
  exact hΔ.mono_right (Finset.sdiff_subset_sdiff (DRS.referents_subset_varFinset K)
    subset_rfl)

/-! ### Growing the base

Adding referents `Δ` to the base pins the output to the input on `Δ` and changes nothing else,
unless `Δ` captures a referent that a sub-DRS declares outside the base, freezing an existential.
Re-declaring a base referent is inert, so `Δ` may meet the base freely. -/

mutual
/-- Growing the base by `Δ` pins the output to the input on `Δ`. -/
theorem DRS.toRelAt_union_iff {X Δ : Finset V} (K : DRS L V)
    (hΔ : Disjoint Δ (K.varFinset \ X)) (hfv : K.freeVarFinset ⊆ X) {f g : V → M} :
    DRS.toRelAt (X ∪ Δ) K f g ↔ DRS.toRelAt X K f g ∧ Set.EqOn g f ↑Δ := by
  match K with
  | ⟨U, cs⟩ =>
    simp only [DRS.toRelAt_mk, Finset.coe_union, Set.eqOn_union]
    rw [Finset.union_right_comm X Δ U, Condition.holdsAllAt_union cs
      (hΔ.mono_right (Finset.sdiff_subset_sdiff Finset.subset_union_right
        Finset.subset_union_left)) (DRS.freeVarFinset_subset_iff.mp hfv)]
    tauto
theorem Condition.holdsAt_union {X Δ : Finset V} (c : Condition L V)
    (hΔ : Disjoint Δ (c.varFinset \ X)) (hfv : c.freeVarFinset ⊆ X) {g : V → M} :
    Condition.holdsAt (X ∪ Δ) c g ↔ Condition.holdsAt X c g := by
  match c with
  | .atom _ => exact Iff.rfl
  | .eq _ _ => exact Iff.rfl
  | .neg K =>
    simp only [Condition.holdsAt_neg, DRS.toRelAt_union_iff K hΔ hfv,
      DRS.exists_toRelAt_and_eqOn_iff hΔ hfv]
  | .imp a c =>
    rw [Condition.varFinset_imp, Finset.union_sdiff_distrib, Finset.disjoint_union_right] at hΔ
    rw [Condition.freeVarFinset_imp, Finset.union_subset_iff] at hfv
    have hfvc : DRS.freeVarFinset c ⊆ X ∪ a.referents := sdiff_le_iff'.mp hfv.2
    have hΔc : Disjoint Δ (DRS.varFinset c \ (X ∪ a.referents)) :=
      hΔ.2.mono_right (Finset.sdiff_subset_sdiff subset_rfl Finset.subset_union_left)
    simp only [Condition.holdsAt_imp, Finset.union_right_comm X Δ a.referents,
      DRS.toRelAt_union_iff a hΔ.1 hfv.1, DRS.toRelAt_union_iff c hΔc hfvc,
      DRS.exists_toRelAt_and_eqOn_iff hΔc hfvc, and_imp]
    refine ⟨fun h g₁ h₁ => ?_, fun h g₁ h₁ _ => h g₁ h₁⟩
    have heq := DRS.eqOn_piecewise_of_toRelAt (hΔ.1.mono_right (Finset.sdiff_subset_sdiff
      (DRS.referents_subset_varFinset a) subset_rfl)) h₁
    exact (h _ ((DRS.toRelAt_congr_right a hfv.1 heq.symm).mp h₁)
      fun _ hx => Finset.piecewise_eq_of_mem _ _ _ hx).imp
        fun _ => (DRS.toRelAt_congr_left _ c heq).mp
  | .dis l r =>
    rw [Condition.varFinset_dis, Finset.union_sdiff_distrib, Finset.disjoint_union_right] at hΔ
    rw [Condition.freeVarFinset_dis, Finset.union_subset_iff] at hfv
    simp only [Condition.holdsAt_dis, exists_or, DRS.toRelAt_union_iff l hΔ.1 hfv.1,
      DRS.toRelAt_union_iff r hΔ.2 hfv.2, DRS.exists_toRelAt_and_eqOn_iff hΔ.1 hfv.1,
      DRS.exists_toRelAt_and_eqOn_iff hΔ.2 hfv.2]
theorem Condition.holdsAllAt_union {X Δ : Finset V} (cs : List (Condition L V))
    (hΔ : Disjoint Δ (Condition.varFinsetL cs \ X)) (hfv : Condition.freeVarFinsetL cs ⊆ X)
    {g : V → M} :
    Condition.holdsAllAt (X ∪ Δ) cs g ↔ Condition.holdsAllAt X cs g := by
  match cs with
  | [] => exact Iff.rfl
  | c :: cs =>
    rw [Condition.varFinsetL_cons, Finset.union_sdiff_distrib, Finset.disjoint_union_right] at hΔ
    rw [Condition.freeVarFinsetL_cons, Finset.union_subset_iff] at hfv
    exact and_congr (Condition.holdsAt_union c hΔ.1 hfv.1)
      (Condition.holdsAllAt_union cs hΔ.2 hfv.2)
end

/-! ### The Merging Lemma -/

/-- The Merging Lemma: `K₁ ⊕ K₂` denotes the composition of `K₁` with `K₂` at the grown base,
when the universe of `K₂` avoids the referents the sub-DRSs of `K₁` declare outside it. -/
theorem DRS.toRelAt_merge {X : Finset V} (K₁ K₂ : DRS L V) (h₁ : K₁.freeVarFinset ⊆ X)
    (hfresh : Disjoint K₂.referents
      (Condition.varFinsetL K₁.conditions \ (X ∪ K₁.referents))) :
    (DRS.toRelAt X (K₁.merge K₂) : (V → M) → (V → M) → Prop) =
      Relation.Comp (DRS.toRelAt X K₁) (DRS.toRelAt (X ∪ K₁.referents) K₂) := by
  obtain ⟨U₁, c₁⟩ := K₁
  obtain ⟨U₂, c₂⟩ := K₂
  have hfvc₁ := DRS.freeVarFinset_subset_iff.mp h₁
  funext f g
  apply propext
  simp only [DRS.merge, DRS.toRelAt_mk, Condition.holdsAllAt_append, Relation.Comp]
  rw [← Finset.union_assoc, Condition.holdsAllAt_union c₁ hfresh hfvc₁]
  constructor
  · rintro ⟨hag, hh₁, hh₂⟩
    exact ⟨g, ⟨hag, hh₁⟩, Set.eqOn_refl g _, hh₂⟩
  · rintro ⟨h, ⟨hhf, hh₁⟩, hgh, hh₂⟩
    exact ⟨(hgh.mono (Finset.coe_subset.mpr Finset.subset_union_left)).trans hhf,
      (Condition.holdsAllAt_congr c₁ hfvc₁ hgh).mpr hh₁, hh₂⟩

/-! ### Reconciliation with the box relation

On reuse-free DRSs (`DRS.ReuseFreeAt`, `DRS/Basic.lean`) every output of the box relation is an
output of the persistence semantics, and an output of the persistence semantics, reset to the
input off the universe, is an output of the box relation. On a DRS that re-declares a referent
the two diverge (Muskens's fn. 4; witness in `Studies/Muskens1996.lean`). -/

mutual
theorem DRS.toRelAt_of_toRel {X : Finset V} (K : DRS L V) (hrf : DRS.ReuseFreeAt X K)
    (hfv : K.freeVarFinset ⊆ X) {g g' : V → M} (h : (g, g') ∈ DRS.toRel K) :
    DRS.toRelAt X K g g' := by
  match K with
  | ⟨U, cs⟩ =>
    rw [DRS.reuseFreeAt_mk] at hrf
    obtain ⟨hag, hh⟩ := (DRS.toRel_iff _ _ _).1 h
    exact ⟨fun x hx => hag x (Finset.disjoint_left.mp hrf.1 hx),
      (Condition.verifiesAll_iff_holdsAllAt cs hrf.2 (DRS.freeVarFinset_subset_iff.mp hfv)).mp hh⟩
theorem DRS.toRel_of_toRelAt {X : Finset V} (K : DRS L V) (hrf : DRS.ReuseFreeAt X K)
    (hfv : K.freeVarFinset ⊆ X) {g g' : V → M} (h : DRS.toRelAt X K g g') :
    ∃ g'', (g, g'') ∈ DRS.toRel K ∧ Set.EqOn g'' g' ↑(X ∪ K.referents) := by
  match K with
  | ⟨U, cs⟩ =>
    rw [DRS.reuseFreeAt_mk] at hrf
    have hfvc := DRS.freeVarFinset_subset_iff.mp hfv
    have heq : Set.EqOn (U.piecewise g' g) g' ↑(X ∪ U) := by
      intro x hx
      by_cases hxU : x ∈ U
      · exact Finset.piecewise_eq_of_mem _ _ _ hxU
      · rw [Finset.piecewise_eq_of_notMem _ _ _ hxU]
        exact (h.1 ((Finset.mem_union.mp hx).resolve_right hxU)).symm
    refine ⟨_, (DRS.toRel_iff _ _ _).2 ⟨Box.extends_piecewise _ g g', ?_⟩, heq⟩
    exact (Condition.verifiesAll_iff_holdsAllAt cs hrf.2 hfvc).mpr
      ((Condition.holdsAllAt_congr cs hfvc heq).mpr h.2)
theorem Condition.verifies_iff_holdsAt {X : Finset V} (c : Condition L V)
    (hrf : Condition.ReuseFreeAt X c) (hfv : c.freeVarFinset ⊆ X) {g : V → M} :
    VerifiesCondition g c ↔ Condition.holdsAt X c g := by
  match c with
  | .atom a => exact Iff.rfl
  | .eq u v => exact Iff.rfl
  | .neg K =>
    rw [verifies_neg_toRel, Update.mem_neg, Condition.holdsAt_neg]
    exact not_congr ⟨fun ⟨k, hk⟩ => ⟨k, DRS.toRelAt_of_toRel K hrf hfv hk⟩,
      fun ⟨k, hk⟩ => (DRS.toRel_of_toRelAt K hrf hfv hk).imp fun _ h => h.1⟩
  | .imp a c =>
    rw [Condition.reuseFreeAt_imp] at hrf
    rw [Condition.freeVarFinset_imp, Finset.union_subset_iff] at hfv
    have hfvc : DRS.freeVarFinset c ⊆ X ∪ a.referents := sdiff_le_iff'.mp hfv.2
    rw [verifies_imp_toRel, Update.mem_impl, Condition.holdsAt_imp]
    constructor
    · intro hL g₁ hg₁
      obtain ⟨g₁', hflat, heq⟩ := DRS.toRel_of_toRelAt a hrf.1 hfv.1 hg₁
      obtain ⟨g₂, hg₂⟩ := hL hflat
      exact ⟨g₂, (DRS.toRelAt_congr_left _ c heq).mp (DRS.toRelAt_of_toRel c hrf.2 hfvc hg₂)⟩
    · intro hR g₁ hg₁
      obtain ⟨g₂, hg₂⟩ := hR g₁ (DRS.toRelAt_of_toRel a hrf.1 hfv.1 hg₁)
      exact (DRS.toRel_of_toRelAt c hrf.2 hfvc hg₂).imp fun _ h => h.1
  | .dis l r =>
    rw [Condition.reuseFreeAt_dis] at hrf
    rw [Condition.freeVarFinset_dis, Finset.union_subset_iff] at hfv
    rw [verifies_dis_toRel, Update.mem_disj, Condition.holdsAt_dis, exists_or]
    refine or_congr ⟨fun ⟨k, hk⟩ => ⟨k, DRS.toRelAt_of_toRel l hrf.1 hfv.1 hk⟩,
      fun ⟨k, hk⟩ => (DRS.toRel_of_toRelAt l hrf.1 hfv.1 hk).imp fun _ h => h.1⟩
      ⟨fun ⟨k, hk⟩ => ⟨k, DRS.toRelAt_of_toRel r hrf.2 hfv.2 hk⟩,
      fun ⟨k, hk⟩ => (DRS.toRel_of_toRelAt r hrf.2 hfv.2 hk).imp fun _ h => h.1⟩
theorem Condition.verifiesAll_iff_holdsAllAt {X : Finset V} (cs : List (Condition L V))
    (hrf : Condition.ReuseFreeAllAt X cs) (hfv : Condition.freeVarFinsetL cs ⊆ X)
    {g : V → M} :
    VerifiesAll g cs ↔ Condition.holdsAllAt X cs g := by
  match cs with
  | [] => exact Iff.rfl
  | c :: cs =>
    rw [Condition.reuseFreeAllAt_cons] at hrf
    rw [Condition.freeVarFinsetL_cons, Finset.union_subset_iff] at hfv
    exact and_congr (Condition.verifies_iff_holdsAt c hrf.1 hfv.1)
      (Condition.verifiesAll_iff_holdsAllAt cs hrf.2 hfv.2)
end

/-- On a reuse-free DRS, the box relation and the persistence semantics have the same truth
conditions. -/
theorem DRS.trueRel_iff_toRelAt {X : Finset V} {K : DRS L V} (hrf : DRS.ReuseFreeAt X K)
    (hfv : K.freeVarFinset ⊆ X) (g : V → M) :
    DRS.trueRel K g ↔ ∃ g', DRS.toRelAt X K g g' := by
  rw [DRS.trueRel_iff]
  exact ⟨fun ⟨g', h⟩ => ⟨g', DRS.toRelAt_of_toRel K hrf hfv h⟩,
    fun ⟨g', h⟩ => (DRS.toRel_of_toRelAt K hrf hfv h).imp fun _ hg => hg.1⟩

end Semantics

/-! ### Context change potentials -/

section ContextChange

variable {W : Type*} (interp : W → L.Structure M)

/-- The context change potential of a DRS (Def. 24): at each world, the persistence semantics
in that world's structure, from the base to the base grown by the universe. On a base missing a
free referent of `K`, outside the domain of Def. 24(i), that referent is existentially closed. -/
def DRS.transition (K : DRS L V) (X : Finset V) :
    Transition W M (↑X : Set V) (↑(X ∪ K.referents) : Set V) :=
  Transition.ofTotal (Finset.coe_subset.mpr Finset.subset_union_left)
    fun w => letI := interp w; DRS.toRelAt X K

/-- The context change potential of a DRS only extends assignments (Def. 27(ii)). -/
theorem DRS.transition_isExtension (K : DRS L V) (X : Finset V) :
    (K.transition interp X).IsExtension := by
  rintro w e e' ⟨f, g, rfl, rfl, hrel⟩
  obtain ⟨U, conds⟩ := K
  exact Set.domRestrict_eq_domRestrict_iff.mpr hrel.1.symm

theorem DRS.transition_copy {X X' : Finset V} (K : DRS L V) (hX : X = X') :
    (K.transition interp X).copy (Finset.coe_inj.mpr hX) (by rw [hX]) =
      K.transition interp X' := by
  subst hX; rfl

/-- The information state a proper DRS expresses (Def. 22), its context change potential applied
to the empty state. -/
def DRS.state (K : DRS L V) : State W V M :=
  (K.transition interp ∅).applyState ⊤

theorem DRS.uniformAt_state (K : DRS L V) :
    State.UniformAt ↑K.referents (K.state interp) := by
  simpa [DRS.state] using Transition.uniformAt_applyState (K.transition interp ∅) ⊤

theorem DRS.mem_state {K : DRS L V} {q : Possibility W V (Flat M)} :
    q ∈ K.state interp ↔ q.domain = ↑K.referents ∧ ∃ f g : V → M,
      (letI := interp q.world; DRS.toRelAt ∅ K f g) ∧
        ∀ v ∈ K.referents, q.assignment v = ↑(g v) := by
  constructor
  · rintro ⟨hq, p, hpI, hp, hw, e, e', he, he', f, g, hf, hg, hrel⟩
    refine ⟨by simpa using hq, f, g, hrel, fun v hv => ?_⟩
    have hv' : v ∈ (↑(∅ ∪ K.referents) : Set V) := by simpa using hv
    rw [he' ⟨v, hv'⟩, ← hg]
    rfl
  · rintro ⟨hq, f, g, hrel, hvals⟩
    refine ⟨by simpa using hq, ⟨q.world, fun _ => ⊥⟩, ⟨q.world, rfl⟩, ?_, rfl,
      (↑(∅ : Finset V) : Set V).domRestrict f, (↑(∅ ∪ K.referents) : Set V).domRestrict g,
      fun v => absurd v.2 (by simp), fun v => hvals v.1 (by simpa using v.2), f, g, rfl, rfl,
      hrel⟩
    ext v
    exact iff_of_false (fun h => h rfl) (by simp)

/-- The proposition the state of a DRS determines (Def. 23(v)) is the set of worlds where the DRS
is true, for a proper DRS the proposition it expresses (Def. 20). -/
theorem DRS.image_world_state (K : DRS L V) :
    Possibility.world '' K.state interp =
      {w | ∃ f g : V → M, letI := interp w; DRS.toRelAt ∅ K f g} := by
  ext w
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨-, f, g, h, -⟩ := (DRS.mem_state interp).mp hq
    exact ⟨f, g, h⟩
  · rintro ⟨f, g, h⟩
    refine ⟨⟨w, fun v => if v ∈ K.referents then ↑(g v) else ⊥⟩,
      (DRS.mem_state interp).mpr ⟨?_, f, g, h, fun v hv => ite_eq_left hv⟩, rfl⟩
    ext v
    by_cases hv : v ∈ K.referents <;> simp [hv]

/-- Sequencing the context change potentials of two DRSs gives that of their merge, repackaged
along the associativity of the grown bases. -/
theorem DRS.transition_merge {X : Finset V} (K₁ K₂ : DRS L V) (h₁ : K₁.freeVarFinset ⊆ X)
    (hfresh : Disjoint K₂.referents
      (Condition.varFinsetL K₁.conditions \ (X ∪ K₁.referents))) :
    (K₁.transition interp X).comp (K₂.transition interp (X ∪ K₁.referents)) =
      ((K₁.merge K₂).transition interp X).copy rfl
        (by rw [DRS.referents_merge, ← Finset.union_assoc]) := by
  have hS : Transition.ReadsAt (W := W) ↑(X ∪ K₁.referents)
      fun w => letI := interp w; DRS.toRelAt (M := M) (X ∪ K₁.referents) K₂ :=
    fun w _ _ _ h => letI := interp w; DRS.toRelAt_congr_left _ K₂ h
  unfold DRS.transition
  rw [Transition.ofTotal_comp hS, Transition.ofTotal_copy]
  exact Transition.ofTotal_congr _ _
    (funext fun w => letI := interp w; (DRS.toRelAt_merge K₁ K₂ h₁ hfresh).symm)

/-- The context change potential of a DRS takes the state of a proper context DRS to the state of
their merge, as the chapter observes of (43) after Def. 24. -/
theorem DRS.state_merge (K₁ K₂ : DRS L V) (h₁ : K₁.IsProper)
    (hfresh : Disjoint K₂.referents (Condition.varFinsetL K₁.conditions \ K₁.referents)) :
    (K₂.transition interp K₁.referents).applyState (K₁.state interp) =
      (K₁.merge K₂).state interp := by
  simp only [DRS.state]
  rw [← DRS.transition_copy interp K₂ (Finset.empty_union K₁.referents),
    Transition.applyState_copy, ← Transition.applyState_comp,
    DRS.transition_merge interp K₁ K₂ (Finset.subset_empty.mpr h₁) (by rwa [Finset.empty_union]),
    Transition.applyState_copy]

end ContextChange

end DRT
