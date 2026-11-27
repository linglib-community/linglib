/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Correspondence.Basic
public import Mathlib.Data.Fintype.Prod

/-!
# The correspondence of a relation between two families

Given a relation `R` between two types and a family of elements of each, indexed by positions,
we define `Correspondence.ofRel R a b` as the correspondence of all pairs of positions whose
members bear `R`. It is monotone in `R` (`Correspondence.ofRel_mono`), its converse is the
correspondence of the converse relation (`Correspondence.inv_ofRel`), and MAX is satisfied on it
exactly when every member of the first family bears `R` to some member of the second
(`Correspondence.maxViol_ofRel_eq_zero_iff`).

For the positions of two lists, MAX and DEP on this correspondence are counts over the lists
(`Correspondence.maxViol_ofRel_get`, `Correspondence.depViol_ofRel_get`).

## References

* [J. J. McCarthy and A. Prince, *Faithfulness and Reduplicative Identity*
  (1995)][mccarthy-prince-1995]
-/

@[expose] public section

namespace OptimalityTheory.Correspondence

open scoped SetRel

variable {ι κ μ : Type*}

section OfRel

variable {β γ : Type*} [Fintype ι] [Fintype κ] (R S : β → γ → Prop) [DecidableRel R]
  [DecidableRel S] (a : ι → β) (b : κ → γ)

/-- The correspondence of all pairs of positions of two families whose members bear `R`. -/
def ofRel : Correspondence ι κ := Finset.univ.filter fun p ↦ R (a p.1) (b p.2)

variable {R S a b}

@[simp] theorem mem_ofRel {i : ι} {j : κ} : (i, j) ∈ ofRel R a b ↔ R (a i) (b j) := by
  simp [ofRel]

theorem inv_ofRel : (ofRel R a b).inv = ofRel (fun y x ↦ R x y) b a := by
  ext ⟨j, i⟩; simp

theorem ofRel_mono (h : ∀ i j, R (a i) (b j) → S (a i) (b j)) : ofRel R a b ⊆ ofRel S a b :=
  fun ⟨i, j⟩ hp ↦ mem_ofRel.2 (h i j (mem_ofRel.1 hp))

theorem ofRel_and [DecidableEq ι] [DecidableEq κ] :
    ofRel (fun x y ↦ R x y ∧ S x y) a b = ofRel R a b ∩ ofRel S a b := by
  ext ⟨i, j⟩; simp

/-- MAX is satisfied on the correspondence of `R` exactly when every member of the first family
bears `R` to some member of the second. -/
theorem maxViol_ofRel_eq_zero_iff [DecidableEq ι] :
    (ofRel R a b).maxViol = 0 ↔ ∀ i, ∃ j, R (a i) (b j) := by
  rw [maxViol_eq_zero_iff, Set.eq_univ_iff_forall]
  exact forall_congr' fun i ↦
    ⟨fun ⟨j, h⟩ ↦ ⟨j, mem_ofRel.1 h⟩, fun ⟨j, h⟩ ↦ ⟨j, mem_ofRel.2 h⟩⟩

end OfRel

section OfRelGet

variable {β γ : Type*} (R : β → γ → Prop) [DecidableRel R] (l : List β) (m : List γ)

/-- MAX on the correspondence of `R` between the positions of two lists counts the members of the
first bearing `R` to no member of the second. -/
theorem maxViol_ofRel_get :
    (ofRel R l.get m.get).maxViol = l.countP fun a ↦ ∀ b ∈ m, ¬R a b := by
  have hset : Finset.univ \ (ofRel R l.get m.get).image Prod.fst =
      Finset.univ.filter fun i : Fin l.length ↦ ∀ b ∈ m, ¬R (l.get i) b := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image, mem_ofRel,
      Prod.exists, exists_and_right, exists_eq_right, not_exists, Finset.mem_filter]
    exact ⟨fun h b hb ↦ by obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hb; exact h j,
      fun h j ↦ h _ (List.get_mem ..)⟩
  have hcount : l.countP (fun a ↦ ∀ b ∈ m, ¬R a b) =
      ((List.finRange l.length).filter fun i ↦ ∀ b ∈ m, ¬R (l.get i) b).length := by
    calc l.countP (fun a ↦ ∀ b ∈ m, ¬R a b)
        = ((List.finRange l.length).map l.get).countP fun a ↦ ∀ b ∈ m, ¬R a b := by
          rw [List.map_get_finRange]
      _ = _ := by rw [List.countP_map, List.countP_eq_length_filter]; rfl
  rw [maxViol, hset, hcount, ← List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)]
  congr 1
  ext i
  simp

/-- DEP on the correspondence of `R` between the positions of two lists counts the members of the
second to which no member of the first bears `R`. -/
theorem depViol_ofRel_get :
    (ofRel R l.get m.get).depViol = m.countP fun b ↦ ∀ a ∈ l, ¬R a b := by
  rw [depViol, inv_ofRel, maxViol_ofRel_get]

variable {R l m}

theorem maxViol_ofRel_get_eq_zero_iff :
    (ofRel R l.get m.get).maxViol = 0 ↔ ∀ a ∈ l, ∃ b ∈ m, R a b := by
  simp [maxViol_ofRel_get, List.countP_eq_zero]

end OfRelGet

end OptimalityTheory.Correspondence
