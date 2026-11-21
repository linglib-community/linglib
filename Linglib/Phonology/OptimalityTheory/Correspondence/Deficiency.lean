/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Correspondence.OfRel
public import Linglib.Core.Data.List.Matching

/-!
# The deficiency of a relation between two families

MAX of [mccarthy-prince-1995] requires every element of one structure to have a correspondent in
the other, and UNIFORMITY that no element of the second have several correspondents in the first.
Where the correspondents an element may take are given by a relation `R` between two families of
constituents, `List.deficiency R l m` counts the members of `l` left unpaired when each member of
`m` is paired with at most one of them: the length of `l` less the matching number of `R`. It is
the least number of violations of MAX among the correspondences within
`Correspondence.ofRel R l.get m.get` that satisfy UNIFORMITY
(`Correspondence.deficiency_le_maxViol`, `Correspondence.exists_maxViol_eq_deficiency`).

MAX of the whole relation, which is alignment along `R`, is therefore at most the deficiency
(`Correspondence.maxViol_ofRel_le_deficiency`), and the deficiency is at most MAX of a relation
contained in `R` that relates no two members to one (`Correspondence.deficiency_le_maxViol_ofRel`).

## References

* [mccarthy-prince-1995]
-/

@[expose] public section

namespace OptimalityTheory.Correspondence

variable {β γ : Type*} {R : β → γ → Prop} [DecidableRel R] [DecidableEq γ] {l : List β}
  {m : List γ}

/-- A correspondence within `R` that violates UNIFORMITY nowhere violates MAX at least
`l.deficiency R m` times. -/
theorem deficiency_le_maxViol {ℜ : Correspondence (Fin l.length) (Fin m.length)}
    (hR : ℜ ⊆ ofRel R l.get m.get) (hU : ℜ.uniformityViol = 0) :
    l.deficiency R m ≤ ℜ.maxViol := by
  rcases ℜ.eq_empty_or_nonempty with rfl | ⟨⟨i₀, j₀⟩, -⟩
  · simp [List.deficiency, Correspondence.maxViol]
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
      exact fun i hi ↦ (mem_ofRel (R := R) (a := l.get) (b := m.get)).1 (hR (hf i (hmem i hi))),
      by simp⟩
  have hmax : ℜ.maxViol = l.length - (ℜ.image Prod.fst).card := by
    simp [Correspondence.maxViol, Finset.card_univ_sdiff]
  simp only [List.deficiency, hmax, hcard]
  omega

/-- Some correspondence within `R` that violates UNIFORMITY nowhere violates MAX exactly
`l.deficiency R m` times. -/
theorem exists_maxViol_eq_deficiency (R : β → γ → Prop) [DecidableRel R] (l : List β)
    (m : List γ) : ∃ ℜ ⊆ ofRel R l.get m.get, ℜ.uniformityViol = 0 ∧
      ℜ.maxViol = l.deficiency R m := by
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
  have hR : ℜ ⊆ ofRel R l.get m.get := fun ⟨i, j⟩ h ↦ by
    obtain ⟨k, -, hk'⟩ := Finset.mem_image.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk'
    have := hget k k.2 (hlen ▸ k.2)
    rw [he k] at this
    exact mem_ofRel.2 this
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
  simp only [List.deficiency, hmax]
  omega

/-- MAX of the whole relation is at most its deficiency. -/
theorem maxViol_ofRel_le_deficiency (R : β → γ → Prop) [DecidableRel R] (l : List β)
    (m : List γ) : (ofRel R l.get m.get).maxViol ≤ l.deficiency R m := by
  obtain ⟨ℜ, hR, -, h⟩ := exists_maxViol_eq_deficiency R l m
  exact h ▸ maxViol_anti hR

/-- Where `S` is contained in `R` and no two members of a duplicate-free family bear `S` to one
member, the deficiency of `R` is at most MAX of `S`. -/
theorem deficiency_le_maxViol_ofRel {S : β → γ → Prop} [DecidableRel S] (hl : l.Nodup)
    (hSR : ∀ a ∈ l, ∀ b, S a b → R a b)
    (hS : ∀ a ∈ l, ∀ a' ∈ l, ∀ b, S a b → S a' b → a = a') :
    l.deficiency R m ≤ (ofRel S l.get m.get).maxViol :=
  deficiency_le_maxViol (ofRel_mono fun i _ h ↦ hSR _ (l.get_mem i) _ h)
    ((uniformityViol_eq_zero_iff _).2 fun i i' _ h h' ↦ hl.get_inj_iff.1
      (hS _ (l.get_mem i) _ (l.get_mem i') _ (mem_ofRel.1 (Finset.mem_coe.1 h))
        (mem_ofRel.1 (Finset.mem_coe.1 h'))))

-- Two members related to one member of the other family: each is aligned, one goes unpaired.
example : (ofRel (fun a b : ℕ ↦ a ≤ b) [0, 1].get [1].get).maxViol = 0 := by decide
example : [0, 1].deficiency (fun a b : ℕ ↦ a ≤ b) [1] = 1 := by decide

end OptimalityTheory.Correspondence
