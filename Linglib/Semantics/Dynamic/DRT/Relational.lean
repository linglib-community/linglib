module

public import Linglib.Semantics.Dynamic.DRT.Translation
public import Linglib.Semantics.Dynamic.RegisterStructure

/-!
# The relational semantics of DRSs

This file interprets a DRS as a relation between embeddings. The relation of a DRS relates an
input embedding to the outputs that differ from it at most on the universe and verify the DRS. It
is the box `Update.box` of `Semantics/Dynamic/RegisterStructure.lean` over the universe, at the
register structure of embeddings, so Muskens's relational semantics of DRT is the general one of
boxes. A DRS is true under an input when some output is related to it.

## Main definitions

* `DRT.DRS.toRel`: the relation of a DRS.
* `DRT.DRS.trueRel`: truth, the domain of that relation.

## Main statements

* `DRT.verifies_neg_toRel`: complex conditions are the connectives of `Update` on these relations.
* `DRT.DRS.toRel_merge`: under freshness, `merge` denotes composition, by `Update.box_comp_box`.
* `DRT.DRS.trueRel_iff_exists_verifies`: on a reuse-free DRS, truth agrees with partial embeddings.

## Implementation notes

Muskens restricts the equivalence of his semantics with the standard one to constructs without
constant discourse referents, which the DRSs here do not have.

## References

* [muskens-1996]
* [groenendijk-stokhof-1991]
-/

@[expose] public section

open FirstOrder FirstOrder.Language
open DynamicSemantics (Update RegisterStructure)
open DynamicSemantics.Update (neg impl disj box box_comp_box mem_box_iff)
open SetRel

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {M : Type x} [L.Structure M] [DecidableEq V]

/-! ### The relation of a DRS -/

/-- The box relation of a DRS (SEM3) is the box over its universe testing its conditions. -/
def DRS.toRel (K : DRS L V) : Update (V → M) :=
  box K.referents {a | VerifiesTotal a K}

@[simp] theorem DRS.toRel_iff (K : DRS L V) (a a' : V → M) :
    a ~[DRS.toRel K] a' ↔ K.Extends a a' ∧ VerifiesTotal a' K :=
  mem_box_iff

/-- A DRS is *true* under an input embedding `a` iff some output embedding is
related to it, the domain of the box relation. -/
def DRS.trueRel (K : DRS L V) (a : V → M) : Prop := a ∈ (DRS.toRel K).dom

theorem DRS.trueRel_iff (K : DRS L V) (a : V → M) :
    DRS.trueRel K a ↔ ∃ a', a ~[DRS.toRel K] a' := Iff.rfl

theorem DRS.trueRel_iff_exists_extends (K : DRS L V) (a : V → M) :
    DRS.trueRel K a ↔ ∃ a', K.Extends a a' ∧ VerifiesTotal a' K := by
  simp only [DRS.trueRel_iff, DRS.toRel_iff]

/-! ### The connectives (SEM2) -/

/-- A negated sub-DRS is the spine's `neg` of its box relation. -/
theorem verifies_neg_toRel (K : DRS L V) (f : V → M) :
    VerifiesConditionTotal f (.neg K) ↔ f ∈ neg (DRS.toRel K) := by
  simp only [verifiesTotal_neg, DynamicSemantics.Update.mem_neg, DRS.toRel_iff]

theorem verifies_imp_toRel (a c : DRS L V) (f : V → M) :
    VerifiesConditionTotal f (.imp a c) ↔ f ∈ impl (DRS.toRel a) (DRS.toRel c) := by
  simp only [verifiesTotal_imp, DynamicSemantics.Update.mem_impl, DRS.toRel_iff, and_imp]

theorem verifies_dis_toRel (l r : DRS L V) (f : V → M) :
    VerifiesConditionTotal f (.dis l r) ↔ f ∈ disj (DRS.toRel l) (DRS.toRel r) := by
  simp only [verifiesTotal_dis, DynamicSemantics.Update.mem_disj, DRS.toRel_iff]

/-! ### Truth -/

/-- A DRS is true under an input exactly when its first-order translation is realized there. -/
theorem DRS.trueRel_iff_realize_toFormula (K : DRS L V) (a : V → M) :
    DRS.trueRel K a ↔ (K.toFormula).Realize a :=
  (DRS.trueRel_iff_exists_extends K a).trans (DRS.realize_toFormula K a).symm

/-- Truth reads the input embedding only at the free referents. -/
theorem DRS.dependsOn_trueRel (K : DRS L V) :
    DependsOn (DRS.trueRel (M := M) K) ↑K.freeVarFinset := fun _ _ h ↦ by
  simpa only [DRS.trueRel_iff_exists_extends] using dependsOn_exists_extends_verifiesTotal K h

/-- Renaming along a bijection transports dynamic truth, so alphabetic variants have the same
truth conditions. -/
theorem DRS.trueRel_map {W : Type*} [DecidableEq W] (e : V ≃ W)
    (K : DRS L V) (a : W → M) :
    DRS.trueRel (K.map e) a ↔ DRS.trueRel K (a ∘ e) := by
  simpa only [DRS.trueRel_iff_exists_extends] using exists_extends_verifiesTotal_map e a K

/-! ### The Merging Lemma -/

/-- When the universe of `K₂` is fresh for the conditions of `K₁`, `K₁ ⊕ K₂` denotes the composition
of their box relations (the Merging Lemma of §II.2). -/
theorem DRS.toRel_merge (K₁ K₂ : DRS L V)
    (hfresh : Disjoint K₂.referents (Condition.varFinsetL K₁.conditions)) :
    (DRS.toRel (K₁.merge K₂) : Update (V → M)) = DRS.toRel K₁ ○ DRS.toRel K₂ := by
  rw [DRS.toRel, DRS.toRel, DRS.toRel, box_comp_box fun r hr ↦ ?_]
  · congr 1
    ext a
    simp
  · rw [RegisterStructure.notMem_dimSet_iff]
    intro g e
    rw [RegisterStructure.extend_eq_update]
    refine (dependsOn_verifiesTotal K₁ fun y hy ↦ Function.update_of_ne ?_ e g).to_iff
    rintro rfl
    exact Finset.disjoint_left.1 hfresh hr
      (Condition.freeVarFinsetL_subset_varFinsetL _ (Finset.mem_coe.1 hy))

/-! ### Agreement with partial embeddings -/

/-- On a reuse-free DRS, Muskens's relational truth from a total input agrees with the partial
semantics from the partial reading of that input. -/
theorem DRS.trueRel_iff_exists_verifies {X : Finset V} {K : DRS L V}
    (hrf : K.ReuseFreeAt X) (hfv : K.freeVarFinset ⊆ X)
    {f : PartialAssign V M} {f' : V → M}
    (hdom : f.domain = ↑X) (hff' : ∀ x ∈ X, f x = ↑(f' x)) :
    DRS.trueRel K f' ↔ ∃ g, K.Verifies f g :=
  (DRS.trueRel_iff_exists_extends K f').trans
    (DRS.exists_extends_verifiesTotal_iff_exists_verifies hrf hfv hdom hff')

/-- On a proper, reuse-free DRS the two notions of truth agree. -/
theorem DRS.trueRel_iff_isTrue {K : DRS L V} (hrf : K.ReuseFreeAt ∅) (hK : K.IsProper)
    (f' : V → M) : DRS.trueRel K f' ↔ K.IsTrue M :=
  DRS.trueRel_iff_exists_verifies hrf (hK ▸ Finset.Subset.refl _)
    (by simp) (fun x hx => absurd hx (Finset.notMem_empty x))

end DRT
