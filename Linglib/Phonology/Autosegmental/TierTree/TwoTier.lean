/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.TierTree.Realization
public import Linglib.Phonology.Autosegmental.TwoTier

/-!
# Two tiers as a tree

On two tiers, with the autosegments over their slots, `AR.twoTier`, a slot bears the labels of
the autosegments linked to it, which is `AR.SurfacesWith` (`mem_melody_twoTier_upper_iff`). A
primitive bears its melody (`melody_primitive`), and a realization by primitives bears at each
slot the melody of its symbol (`melody_prod_map_primitive`), so that taking melodies inverts
realization.

## References

* [goldsmith-1976]
* [jardine-2019]
-/

@[expose] public section

namespace Autosegmental.AR

open Tier

universe u

variable {α β : Type u} {X : AR (TwoTier α β)} {a : α} {j q : ℕ}

/-- The tree of two tiers, the autosegments over their slots. -/
def twoTier : ParentTree Tier := .ofIterate (fun _ ↦ lower) lower 1 fun _ ↦ rfl

theorem dominates_twoTier_upper_iff : X.Dominates twoTier j upper q ↔ X.Link upper lower q j := by
  rw [Dominates, Tier.card]
  simp only [descendants, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_singleton]
  constructor
  · rintro (h | ⟨⟨t, p⟩, hc, h | ⟨⟨t', p'⟩, hc', h⟩⟩)
    · exact absurd (congrArg Prod.fst h) (show upper ≠ lower by decide)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact (mem_children.1 hc).2.2.symm
    · exact absurd (mem_children.1 hc').1.symm (mem_children.1 hc).2.1
  · exact fun h ↦ .inr ⟨(upper, q), mem_children.2 ⟨rfl, by decide, h.symm⟩, .inl rfl⟩

/-- On two tiers, a slot bears the labels of the autosegments linked to it. -/
theorem mem_melody_twoTier_upper_iff : a ∈ X.melody twoTier j upper ↔ X.SurfacesWith a j := by
  simp only [mem_melody_iff_exists_dominates, dominates_twoTier_upper_iff, SurfacesWith]

/-- A primitive bears its melody. -/
theorem melody_primitive {as : List α} {b : β} : (primitive as b).melody twoTier 0 upper = as := by
  have h : ((primitive as b).word upper).zipIdx.filter
      (fun x ↦ (primitive as b).Dominates twoTier 0 upper x.2) =
      ((primitive as b).word upper).zipIdx :=
    List.filter_eq_self.2 fun x hx ↦ decide_eq_true (dominates_twoTier_upper_iff.2
      (link_primitive.2 ⟨by simpa using List.snd_lt_of_mem_zipIdx hx, rfl⟩))
  rw [melody, h, List.zipIdx_map_fst]
  rfl

/-- A realization by primitives bears at each slot the labels of the melody of its symbol. -/
theorem mem_melody_prod_map_primitive {S : Type*} (as : S → List α) (b : S → β) {w : List S}
    {k : ℕ} :
    a ∈ (w.map fun s ↦ primitive (as s) (b s)).prod.melody twoTier k upper ↔
      ∃ hk : k < w.length, a ∈ as w[k] :=
  (mem_melody_prod_map twoTier _ fun _ ↦ rfl).trans
    (exists_congr fun _ ↦ by rw [melody_primitive])

/-- A realization by primitives bears at each slot the melody of its symbol. -/
theorem melody_prod_map_primitive {S : Type*} (as : S → List α) (b : S → β) {w : List S}
    {k : ℕ} (hk : k < w.length) :
    (w.map fun s ↦ primitive (as s) (b s)).prod.melody twoTier k upper = as w[k] :=
  (melody_prod_map twoTier _ (fun _ ↦ rfl) hk).trans melody_primitive


end Autosegmental.AR
