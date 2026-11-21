/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Constraint.Alignment
public import Linglib.Phonology.OptimalityTheory.Correspondence.Basic
public import Linglib.Core.Data.List.Matching

/-!
# The deficiency of a relation between two families

MAX of [mccarthy-prince-1995] requires every element of one structure to have a correspondent in
the other, and UNIFORMITY that no element of the second have several correspondents in the first.
Where the correspondents an element may take are given by a relation `R` between two families of
constituents, we define `Constraint.deficiency R` to count the members of the first family left
unpaired when each member of the second is paired with at most one of the first: the length of
the family less the matching number of `R`. It is the least number of violations of MAX among the
correspondences between the positions of the two families that lie within `R` and satisfy
UNIFORMITY (`Constraint.deficiency_le_maxViol`, `Constraint.exists_maxViol_eq_deficiency`).
Alignment along `R` is MAX of the largest such relation, the correspondence of all pairs of
positions related by `R` (`Constraint.align_eq_maxViol`).

Pairing demands at least as much as alignment along the same relation, and no more than alignment
along a relation contained in it that relates no two members to one:
`align R ≤ deficiency R ≤ align S` (`Constraint.align_le_deficiency`,
`Constraint.deficiency_le_align`).

## References

* [mccarthy-prince-1995]
-/

@[expose] public section

namespace OptimalityTheory.Constraint

variable {β γ : Type*} (R : β → γ → Prop) [DecidableRel R] [DecidableEq γ]

/-- The deficiency of `R` between two families: one violation for each member of the first left
unpaired by a largest pairing along `R` in which each member of the second answers to at most one
of the first (`List.le_matchingNumber_iff`). -/
def deficiency : Constraint (List β × List γ) := fun x ↦ x.1.length - x.1.matchingNumber R x.2

variable {R}

/-- A member aligned with nothing along `R` is left unpaired along `R`. -/
theorem align_le_deficiency (x : List β × List γ) : align R x ≤ deficiency R x := by
  have h₁ := List.matchingNumber_le_countP (R := R) x.1 x.2
  have h₂ := align_add_countP (R := R) x
  simp only [deficiency]
  omega

/-- Where `S` is contained in `R` and no two members of a duplicate-free family bear `S` to one
member, the members left unpaired along `R` are at most those aligned with nothing along `S`. -/
theorem deficiency_le_align {S : β → γ → Prop} [DecidableRel S] {x : List β × List γ}
    (hx : x.1.Nodup) (hSR : ∀ a ∈ x.1, ∀ b, S a b → R a b)
    (hS : ∀ a ∈ x.1, ∀ a' ∈ x.1, ∀ b, S a b → S a' b → a = a') : deficiency R x ≤ align S x := by
  have h₁ := List.countP_le_matchingNumber hx hSR hS x.2
  have h₂ := align_add_countP (R := S) x
  simp only [deficiency]
  omega

variable {l : List β} {m : List γ}

omit [DecidableEq γ] in
/-- Alignment along `R` is MAX of the correspondence of all pairs of positions related by `R`. -/
theorem align_eq_maxViol (R : β → γ → Prop) [DecidableRel R] (l : List β) (m : List γ) :
    align R (l, m) = Correspondence.maxViol
      (Finset.univ.filter fun p : Fin l.length × Fin m.length ↦ R l[p.1] m[p.2]) := by
  have hset : Finset.univ \ (Finset.univ.filter
      fun p : Fin l.length × Fin m.length ↦ R l[p.1] m[p.2]).image Prod.fst =
        Finset.univ.filter fun i : Fin l.length ↦ ∀ b ∈ m, ¬R l[i] b := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_filter,
      Prod.exists, exists_and_right, exists_eq_right, not_exists]
    exact ⟨fun h b hb ↦ by obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hb; exact h j,
      fun h j ↦ h _ (List.get_mem ..)⟩
  have hcount : l.countP (fun a ↦ ∀ b ∈ m, ¬R a b) =
      ((List.finRange l.length).filter fun i ↦ ∀ b ∈ m, ¬R l[i] b).length := by
    calc l.countP (fun a ↦ ∀ b ∈ m, ¬R a b)
        = ((List.finRange l.length).map l.get).countP fun a ↦ ∀ b ∈ m, ¬R a b := by
          rw [List.map_get_finRange]
      _ = _ := by rw [List.countP_map, List.countP_eq_length_filter]; rfl
  rw [Correspondence.maxViol, hset, align, hcount,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)]
  congr 1
  ext i
  simp

/-- A correspondence between the positions of two families that lies within `R` and violates
UNIFORMITY nowhere violates MAX at least `deficiency R` times. -/
theorem deficiency_le_maxViol {ℜ : Correspondence (Fin l.length) (Fin m.length)}
    (hR : ∀ i j, (i, j) ∈ ℜ → R l[i] m[j]) (hU : ℜ.uniformityViol = 0) :
    deficiency R (l, m) ≤ ℜ.maxViol := by
  rcases ℜ.eq_empty_or_nonempty with rfl | ⟨⟨i₀, j₀⟩, -⟩
  · simp [deficiency, Correspondence.maxViol]
  have : Nonempty (Fin m.length) := ⟨j₀⟩
  have hdom : ∀ i ∈ ℜ.image Prod.fst, ∃ j, (i, j) ∈ ℜ := fun i hi ↦ by
    obtain ⟨⟨i', j⟩, h, rfl⟩ := Finset.mem_image.1 hi
    exact ⟨j, h⟩
  choose! f hf using hdom
  have hU := (Correspondence.uniformityViol_eq_zero_iff ℜ).1 hU
  let idxs := (List.finRange l.length).filter (· ∈ ℜ.image Prod.fst)
  have hmem : ∀ i ∈ idxs, i ∈ ℜ.image Prod.fst := fun i hi ↦ by simpa [idxs] using hi
  have hnd : idxs.Nodup := (List.nodup_finRange _).filter _
  have hcard : (ℜ.image Prod.fst).card = idxs.length := by
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1
    ext i
    simp [idxs]
  have hl : (idxs.map l.get).Sublist l := by
    simpa [List.map_get_finRange] using
      (List.filter_sublist (l := List.finRange l.length)).map l.get
  have hm : ((idxs.map f).map m.get).Subperm m := by
    obtain ⟨js, hp, hs⟩ := List.subperm_of_subset (hnd.map_on fun i hi i' hi' (h : f i = f i') ↦
      hU (Finset.mem_coe.2 (hf i (hmem i hi)))
        (Finset.mem_coe.2 (show (i', f i) ∈ ℜ from h ▸ hf i' (hmem i' hi'))))
      fun j _ ↦ List.mem_finRange j
    exact ⟨js.map m.get, hp.map _, by simpa [List.map_get_finRange] using hs.map m.get⟩
  have hle : idxs.length ≤ l.matchingNumber R m := List.le_matchingNumber_iff.2
    ⟨_, _, hl, hm, by
      rw [List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
      exact fun i hi ↦ hR i (f i) (hf i (hmem i hi)), by simp⟩
  have hmax : ℜ.maxViol = l.length - (ℜ.image Prod.fst).card := by
    simp [Correspondence.maxViol, Finset.card_univ_sdiff]
  simp only [deficiency, hmax, hcard]
  omega

/-- Some correspondence between the positions of two families that lies within `R` and violates
UNIFORMITY nowhere violates MAX exactly `deficiency R` times. -/
theorem exists_maxViol_eq_deficiency (R : β → γ → Prop) [DecidableRel R] (l : List β)
    (m : List γ) : ∃ ℜ : Correspondence (Fin l.length) (Fin m.length),
      (∀ i j, (i, j) ∈ ℜ → R l[i] m[j]) ∧ ℜ.uniformityViol = 0 ∧
        ℜ.maxViol = deficiency R (l, m) := by
  have h₀ : l.matchingNumber R m ≤
      l.matchingNumber (fun a j ↦ R a (m.get j)) (List.finRange m.length) := by
    simpa [List.map_get_finRange] using
      List.matchingNumber_map_right_le (R := R) m.get l (List.finRange m.length)
  obtain ⟨l₁, js, hl, ⟨js', hp, hs⟩, hF, hk⟩ := List.le_matchingNumber_iff.1
    (le_refl (l.matchingNumber (fun a j ↦ R a (m.get j)) (List.finRange m.length)))
  obtain ⟨e, he⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.1 hl
  have hnd : js.Nodup := hp.nodup_iff.1 (hs.nodup (List.nodup_finRange _))
  obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.1 hF
  let ℜ : Correspondence (Fin l.length) (Fin m.length) :=
    Finset.univ.image fun k : Fin l₁.length ↦ (e k, js.get (k.cast hlen))
  have hR : ∀ i j, (i, j) ∈ ℜ → R l[i] m[j] := fun i j h ↦ by
    obtain ⟨k, -, hk'⟩ := Finset.mem_image.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk'
    have := hget k k.2 (hlen ▸ k.2)
    rw [he k] at this
    simpa using this
  have hU : ℜ.uniformityViol = 0 :=
    (Correspondence.uniformityViol_eq_zero_iff ℜ).2 fun i i' j h h' ↦ by
      obtain ⟨k, -, hk₁⟩ := Finset.mem_image.1 (Finset.mem_coe.1 h)
      obtain ⟨k', -, hk₂⟩ := Finset.mem_image.1 (Finset.mem_coe.1 h')
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk₁
      obtain ⟨rfl, hj⟩ := Prod.mk.inj hk₂
      rw [Fin.cast_injective hlen (hnd.get_inj_iff.1 hj)]
  refine ⟨ℜ, hR, hU, le_antisymm ?_ (deficiency_le_maxViol hR hU)⟩
  have himg : ℜ.image Prod.fst = Finset.univ.image e := by
    simp [ℜ, Finset.image_image, Function.comp_def]
  have hmax : ℜ.maxViol = l.length - l₁.length := by
    simp [Correspondence.maxViol, Finset.card_univ_sdiff, himg,
      Finset.card_image_of_injective _ e.injective]
  simp only [deficiency, hmax]
  omega

-- Two words inside one phrase both align to it, but only one can have it as correspondent.
example : align (· ≤ ·) ([(⟨(0, 1), by decide⟩ : NonemptyInterval ℕ), ⟨(1, 2), by decide⟩],
    [⟨(0, 2), by decide⟩]) = 0 := by
  decide
example : deficiency (· ≤ ·) ([(⟨(0, 1), by decide⟩ : NonemptyInterval ℕ), ⟨(1, 2), by decide⟩],
    [⟨(0, 2), by decide⟩]) = 1 := by
  decide

end OptimalityTheory.Constraint
