/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.Definite`.
-/
module

public import Linglib.Core.Computability.Edge
public import Linglib.Core.Computability.MyhillNerode
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Data.Set.Finite.List

/-!
# Definite languages

This file defines the definite languages and their relatives. A language `L` is *`k`-definite*
when membership of a word is decided by its last `k` letters: any two words with the same
length-`k` suffix are both in `L` or both outside it. Perles, Rabin and Shamir develop the theory
of these languages; *reverse `k`-definite* languages are the mirror image through the length-`k`
prefix, and *generalized `k`-definite* languages are decided by the prefix and suffix together.

## Main definitions

* `Language.IsDefinite`, `Language.IsReverseDefinite`, `Language.IsGeneralizedDefinite`: membership
  factors through the suffix, the prefix, and both.
* `Language.IsFiniteOrCofinite`: `L` or its complement is finite.

## Main results

* `Language.IsDefinite.toIsGeneralizedDefinite`,
  `Language.IsReverseDefinite.toIsGeneralizedDefinite`: definite and reverse definite languages are
  generalized definite.
* `Language.IsDefinite.isRegular`, `Language.IsReverseDefinite.isRegular`,
  `Language.IsGeneralizedDefinite.isRegular`: over a finite alphabet all three are regular.
* `Language.isFiniteOrCofinite_iff_exists_isDefinite_and_isReverseDefinite`: over a finite
  alphabet, a language is finite or cofinite exactly when it is both definite and reverse definite.

## References

* [perles-rabin-shamir-1963]
* [pin-mfa]
-/

@[expose] public section

variable {α : Type*}

/-! ### Edge-bridge identities

Two long words are bridged by a word sharing the length-`k` suffix of the first and the
length-`k'` prefix of the second. This is the combinatorial step behind the characterization of
the finite and cofinite languages. -/

private lemma takeAt_right_eq_of_bridge {k k' : ℕ} {w₁ w₂ : List α}
    (hw₁ : k ≤ w₁.length) (_hw₂ : k' ≤ w₂.length) :
    Edge.right.takeAt k (w₂.take k' ++ w₁.rtake k) = Edge.right.takeAt k w₁ := by
  have hk : k ≤ (w₁.rtake k).length := by rw [List.length_rtake]; omega
  rw [Edge.takeAt_right, Edge.takeAt_right, List.rtake_append_of_le_length hk,
    List.rtake_of_length_le (by rw [List.length_rtake]; omega)]

private lemma takeAt_left_eq_of_bridge {k k' : ℕ} {w₁ w₂ : List α}
    (_hw₁ : k ≤ w₁.length) (hw₂ : k' ≤ w₂.length) :
    Edge.left.takeAt k' (w₂.take k' ++ w₁.rtake k) = Edge.left.takeAt k' w₂ := by
  rw [Edge.takeAt_left, Edge.takeAt_left,
    List.take_append_of_le_length (by rw [List.length_take]; omega), List.take_take, min_self]

namespace Language

/-! ### The definite family -/

/-- A language is *`k`-definite* when membership factors through the length-`k` suffix. -/
def IsDefinite (L : Language α) (k : ℕ) : Prop :=
  Function.FactorsThrough (· ∈ L) (Edge.right.takeAt k)

/-- A language is *reverse `k`-definite* when membership factors through the length-`k`
prefix. -/
def IsReverseDefinite (L : Language α) (k : ℕ) : Prop :=
  Function.FactorsThrough (· ∈ L) (Edge.left.takeAt k)

/-- A language is *generalized `k`-definite* when membership factors through the length-`k`
prefix and suffix together. -/
def IsGeneralizedDefinite (L : Language α) (k : ℕ) : Prop :=
  Function.FactorsThrough (· ∈ L) (fun w ↦ (Edge.left.takeAt k w, Edge.right.takeAt k w))

lemma isGeneralizedDefinite_iff_edges {k : ℕ} {L : Language α} :
    L.IsGeneralizedDefinite k ↔
      ∀ ⦃a b⦄, Edge.left.takeAt k a = Edge.left.takeAt k b →
        Edge.right.takeAt k a = Edge.right.takeAt k b → (a ∈ L ↔ b ∈ L) :=
  ⟨fun h _ _ hpre hsuf ↦ iff_of_eq (h (by simp only [hpre, hsuf])),
   fun h _ _ hpair ↦ propext (h (congrArg Prod.fst hpair) (congrArg Prod.snd hpair))⟩

lemma isDefinite_iff_mem_takeAt {k : ℕ} {L : Language α} :
    L.IsDefinite k ↔ ∀ w, w ∈ L ↔ Edge.right.takeAt k w ∈ L := by
  unfold IsDefinite
  rw [Function.factorsThrough_iff_of_idempotent (fun a ↦ Edge.right.takeAt_idem k a)]
  simp only [eq_iff_iff]

lemma isReverseDefinite_iff_mem_takeAt {k : ℕ} {L : Language α} :
    L.IsReverseDefinite k ↔ ∀ w, w ∈ L ↔ Edge.left.takeAt k w ∈ L := by
  unfold IsReverseDefinite
  rw [Function.factorsThrough_iff_of_idempotent (fun a ↦ Edge.left.takeAt_idem k a)]
  simp only [eq_iff_iff]

/-- A language is *finite or cofinite* when it or its complement is finite. -/
def IsFiniteOrCofinite (L : Language α) : Prop :=
  L.Finite ∨ Lᶜ.Finite

theorem isDefinite_setOf_right (k : ℕ) (P : Set (List α)) :
    IsDefinite {w | Edge.right.takeAt k w ∈ P} k :=
  fun _ _ hab ↦ congrArg (· ∈ P) hab

theorem isReverseDefinite_setOf_left (k : ℕ) (P : Set (List α)) :
    IsReverseDefinite {w | Edge.left.takeAt k w ∈ P} k :=
  fun _ _ hab ↦ congrArg (· ∈ P) hab

/-! ### Monotonicity in the window -/

theorem IsDefinite.mono {k k' : ℕ} {L : Language α} (h : L.IsDefinite k) (hk : k ≤ k') :
    L.IsDefinite k' :=
  fun _ _ hab ↦ h (Edge.takeAt_eq_of_le .right hk hab)

theorem IsReverseDefinite.mono {k k' : ℕ} {L : Language α} (h : L.IsReverseDefinite k)
    (hk : k ≤ k') : L.IsReverseDefinite k' :=
  fun _ _ hab ↦ h (Edge.takeAt_eq_of_le .left hk hab)

theorem IsGeneralizedDefinite.mono {k k' : ℕ} {L : Language α} (h : L.IsGeneralizedDefinite k)
    (hk : k ≤ k') : L.IsGeneralizedDefinite k' :=
  fun _ _ hab ↦ h (Prod.ext (Edge.takeAt_eq_of_le .left hk (congrArg Prod.fst hab))
    (Edge.takeAt_eq_of_le .right hk (congrArg Prod.snd hab)))

/-! ### Affix languages -/

/-- The words beginning with `xs`. -/
def ofPrefix (xs : List α) : Language α := {w | xs <+: w}

/-- The words ending in `xs`. -/
def ofSuffix (xs : List α) : Language α := {w | xs <:+ w}

@[simp] theorem mem_ofPrefix {xs w : List α} : w ∈ ofPrefix xs ↔ xs <+: w := Iff.rfl

@[simp] theorem mem_ofSuffix {xs w : List α} : w ∈ ofSuffix xs ↔ xs <:+ w := Iff.rfl

theorem isReverseDefinite_ofPrefix (xs : List α) : (ofPrefix xs).IsReverseDefinite xs.length :=
  fun a b hab ↦ by
    simp only [Edge.takeAt_left] at hab
    simp only [mem_ofPrefix, List.prefix_iff_eq_take, hab]

theorem isDefinite_ofSuffix (xs : List α) : (ofSuffix xs).IsDefinite xs.length :=
  fun a b hab ↦ by
    simp only [mem_ofSuffix, List.suffix_iff_eq_drop]
    exact congrArg (xs = ·) hab

/-! ### Reverse duality -/

private lemma takeAt_left_reverse (k : ℕ) (l : List α) :
    Edge.left.takeAt k l.reverse = (Edge.right.takeAt k l).reverse := by
  simp [Edge.takeAt_left, Edge.takeAt_right, List.rtake_eq_reverse_take_reverse]

private lemma takeAt_right_reverse (k : ℕ) (l : List α) :
    Edge.right.takeAt k l.reverse = (Edge.left.takeAt k l).reverse := by
  simp [Edge.takeAt_left, Edge.takeAt_right, List.rtake_eq_reverse_take_reverse]

theorem isReverseDefinite_iff_isDefinite_reverse {k : ℕ} {L : Language α} :
    L.IsReverseDefinite k ↔ L.reverse.IsDefinite k := by
  constructor
  · intro h a b hab
    have key : Edge.left.takeAt k a.reverse = Edge.left.takeAt k b.reverse := by
      rw [takeAt_left_reverse, takeAt_left_reverse, hab]
    simpa only [Language.mem_reverse] using h key
  · intro h a b hab
    have key : Edge.right.takeAt k a.reverse = Edge.right.takeAt k b.reverse := by
      rw [takeAt_right_reverse, takeAt_right_reverse, hab]
    simpa only [Language.reverse_mem_reverse] using h key

/-! ### Inclusions into the generalized definite languages -/

theorem IsDefinite.toIsGeneralizedDefinite {k : ℕ} {L : Language α}
    (h : L.IsDefinite k) : L.IsGeneralizedDefinite k :=
  fun _ _ hab ↦ h (congrArg Prod.snd hab)

theorem IsReverseDefinite.toIsGeneralizedDefinite {k : ℕ} {L : Language α}
    (h : L.IsReverseDefinite k) : L.IsGeneralizedDefinite k :=
  fun _ _ hab ↦ h (congrArg Prod.fst hab)

/-! ### Regularity -/

theorem IsDefinite.isRegular [Finite α] {k : ℕ} {L : Language α} (h : L.IsDefinite k) :
    L.IsRegular :=
  .of_factorsThrough h (fun _ _ x e ↦ Edge.takeAt_append_congr .right e x)
    (Edge.finite_range_takeAt .right k)

theorem IsReverseDefinite.isRegular [Finite α] {k : ℕ} {L : Language α}
    (h : L.IsReverseDefinite k) : L.IsRegular :=
  .of_factorsThrough h (fun _ _ x e ↦ Edge.takeAt_append_congr .left e x)
    (Edge.finite_range_takeAt .left k)

theorem IsGeneralizedDefinite.isRegular [Finite α] {k : ℕ} {L : Language α}
    (h : L.IsGeneralizedDefinite k) : L.IsRegular :=
  .of_factorsThrough h
    (fun _ _ x e ↦ Prod.ext (Edge.takeAt_append_congr .left (congrArg Prod.fst e) x)
      (Edge.takeAt_append_congr .right (congrArg Prod.snd e) x))
    (((Edge.finite_range_takeAt .left k).prod (Edge.finite_range_takeAt .right k)).subset
      (Set.range_subset_iff.2 fun w ↦ ⟨⟨w, rfl⟩, ⟨w, rfl⟩⟩))

/-! ### Finite and cofinite languages -/

theorem isFiniteOrCofinite_of_eventually_constant {L : Language α} {s : Set (List α)}
    (hs : s.Finite) (h : ∀ a ∈ sᶜ, ∀ b ∈ sᶜ, (a ∈ L ↔ b ∈ L)) : L.IsFiniteOrCofinite := by
  by_cases h_witness : ∃ w₀ ∈ sᶜ, w₀ ∈ L
  · obtain ⟨w₀, hw₀_s, hw₀_L⟩ := h_witness
    refine Or.inr (hs.subset ?_)
    intro w hwLc
    by_contra hws
    exact hwLc ((h w hws w₀ hw₀_s).mpr hw₀_L)
  · simp only [not_exists, not_and] at h_witness
    refine Or.inl (hs.subset ?_)
    intro w hwL
    by_contra hws
    exact h_witness w hws hwL

private lemma factorsThrough_takeAt_of_bounded {L : Language α} {N : ℕ} (e : Edge)
    (h_bound : ∀ w ∈ L, w.length ≤ N) :
    Function.FactorsThrough (· ∈ L) (e.takeAt (N + 1)) := by
  refine fun a b hab ↦ ?_
  have hlen : min (N + 1) a.length = min (N + 1) b.length := by
    have := congrArg List.length hab
    rwa [Edge.length_takeAt, Edge.length_takeAt] at this
  by_cases ha : a.length ≤ N
  · have hb : b.length ≤ N := by omega
    rw [Edge.takeAt_of_length_le e (by omega), Edge.takeAt_of_length_le e (by omega)] at hab
    rw [hab]
  · have hb : ¬ b.length ≤ N := by omega
    exact propext ⟨fun h ↦ absurd (h_bound a h) ha, fun h ↦ absurd (h_bound b h) hb⟩

theorem isDefinite_succ_of_forall_length_le {L : Language α} {N : ℕ}
    (h : ∀ w ∈ L, w.length ≤ N) : L.IsDefinite (N + 1) :=
  factorsThrough_takeAt_of_bounded .right h

theorem isReverseDefinite_succ_of_forall_length_le {L : Language α} {N : ℕ}
    (h : ∀ w ∈ L, w.length ≤ N) : L.IsReverseDefinite (N + 1) :=
  factorsThrough_takeAt_of_bounded .left h

private lemma factorsThrough_takeAt_of_cobounded {L : Language α} {N : ℕ} (e : Edge)
    (h_bound : ∀ w ∈ Lᶜ, w.length ≤ N) :
    Function.FactorsThrough (· ∈ L) (e.takeAt (N + 1)) :=
  fun _ _ hab ↦
    propext (not_iff_not.mp (iff_of_eq (factorsThrough_takeAt_of_bounded e h_bound hab)))

private lemma exists_length_bound_of_finite {S : Set (List α)} (h : S.Finite) :
    ∃ N, ∀ w ∈ S, w.length ≤ N :=
  let ⟨N, hN⟩ := (h.image (·.length)).exists_le
  ⟨N, fun w hw ↦ hN _ ⟨w, hw, rfl⟩⟩

theorem IsFiniteOrCofinite.exists_isDefinite_and_isReverseDefinite
    {L : Language α} (h : L.IsFiniteOrCofinite) :
    (∃ k, L.IsDefinite k) ∧ (∃ k', L.IsReverseDefinite k') := by
  rcases h with h | h
  · obtain ⟨N, hN⟩ := exists_length_bound_of_finite h
    exact ⟨⟨N + 1, factorsThrough_takeAt_of_bounded .right hN⟩,
           ⟨N + 1, factorsThrough_takeAt_of_bounded .left hN⟩⟩
  · obtain ⟨N, hN⟩ := exists_length_bound_of_finite h
    exact ⟨⟨N + 1, factorsThrough_takeAt_of_cobounded .right hN⟩,
           ⟨N + 1, factorsThrough_takeAt_of_cobounded .left hN⟩⟩

theorem isFiniteOrCofinite_of_isDefinite_and_isReverseDefinite [Finite α]
    {L : Language α}
    (h : (∃ k, L.IsDefinite k) ∧ (∃ k', L.IsReverseDefinite k')) :
    L.IsFiniteOrCofinite := by
  obtain ⟨⟨k, hD⟩, ⟨k', hR⟩⟩ := h
  refine isFiniteOrCofinite_of_eventually_constant (List.finite_length_lt α (k + k')) ?_
  intro w₁ hw₁ w₂ hw₂
  have hk : k ≤ w₁.length := by rw [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hw₁; omega
  have hk' : k' ≤ w₂.length := by rw [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hw₂; omega
  exact (iff_of_eq (hD (takeAt_right_eq_of_bridge hk hk').symm)).trans
    (iff_of_eq (hR (takeAt_left_eq_of_bridge hk hk')))

theorem isFiniteOrCofinite_iff_exists_isDefinite_and_isReverseDefinite [Finite α]
    {L : Language α} :
    L.IsFiniteOrCofinite ↔
    (∃ k, L.IsDefinite k) ∧ (∃ k', L.IsReverseDefinite k') :=
  ⟨IsFiniteOrCofinite.exists_isDefinite_and_isReverseDefinite,
   isFiniteOrCofinite_of_isDefinite_and_isReverseDefinite⟩

end Language
