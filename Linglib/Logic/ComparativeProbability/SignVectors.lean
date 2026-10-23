module

public import Linglib.Logic.ComparativeProbability.Scott
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Linarith

/-! # Anti-dominating pairs among balanced comparisons on four atoms

A comparison on four atoms is a sign vector `v : Fin 4 → SignType`, with positive side
`posSupport v` and negative side `negSupport v`. Two comparisons are *mergeable* when no atom
carries the same nonzero sign in both, and *anti-dominating* when the positive side of each lies
in the negative side of the other. Every nonempty multiset of pairwise non-mergeable comparisons
with nonempty positive sides that sums to zero contains an anti-dominating pair; this is the
combinatorial core of cancellation on `Fin 4`.

## Main declarations

* `ComparativeProbability.Mergeable`, `ComparativeProbability.AntiDominating`: the two relations
  between comparisons.
* `ComparativeProbability.dotProduct_eq_zero_of_comparisonSum_eq_zero`: an integer functional
  that is nonnegative on a multiset of comparisons summing to zero vanishes on it.
* `ComparativeProbability.exists_antiDominating`: the anti-domination theorem.

## Implementation notes

Every case closes by a *witness*, an integer functional that is nonnegative on the family and
positive on a member, which `dotProduct_eq_zero_of_comparisonSum_eq_zero` rules out; the cases
read the family as the finset of its distinct members. A family of at most three
members falls to the functional reading the signs that one member shares with the others. In a
larger family, a member with a single positive coordinate `k` falls to `e_k` when it has full
support; otherwise it has the shape `+1` at `p`, `0` at `ζ`, `-1` elsewhere, the functional
`e_p + e_ζ` forces a second member of the same shape, and the next iterate closes a 3-cycle that
`e_p + e_i + e_ζ - e_j` refutes. Once every member has two positive coordinates, `𝟙` forces each
to have exactly two of each sign, and a pigeonhole on the three complementary pairs of 2-subsets
of `Fin 4` yields an anti-dominating pair.
-/

@[expose] public section

namespace ComparativeProbability

open Finset

section General

variable {W : Type*}

/-- Two comparisons are mergeable when no atom carries the same nonzero sign in both. -/
def Mergeable (v w : W → SignType) : Prop :=
  Disjoint (posSupport v) (posSupport w) ∧ Disjoint (negSupport v) (negSupport w)

theorem Mergeable.symm {v w : W → SignType} (h : Mergeable v w) : Mergeable w v :=
  ⟨h.1.symm, h.2.symm⟩

/-- Two comparisons are anti-dominating when the positive side of each lies in the negative side
of the other. -/
def AntiDominating (v w : W → SignType) : Prop :=
  posSupport v ⊆ negSupport w ∧ posSupport w ⊆ negSupport v

/-- An integer functional that is nonnegative on a multiset of comparisons summing to zero
vanishes on each of them. -/
theorem dotProduct_eq_zero_of_comparisonSum_eq_zero [Fintype W] {M : Multiset (W → SignType)}
    (hM : comparisonSum M = 0) {u : W → ℤ} (hu : ∀ v ∈ M, 0 ≤ u ⬝ᵥ fun i ↦ (v i : ℤ))
    {v : W → SignType} (hv : v ∈ M) : (u ⬝ᵥ fun i ↦ (v i : ℤ)) = 0 := by
  classical
  have hsum : ∑ w ∈ M.toFinset, (M.count w : ℤ) * (u ⬝ᵥ fun i ↦ (w i : ℤ)) = 0 := by
    have h (i : W) : ∑ w ∈ M.toFinset, (M.count w : ℤ) * w i = 0 := by
      simpa [comparisonSum, Finset.sum_multiset_map_count] using congrFun hM i
    calc ∑ w ∈ M.toFinset, (M.count w : ℤ) * (u ⬝ᵥ fun i ↦ (w i : ℤ))
        = ∑ i, u i * ∑ w ∈ M.toFinset, (M.count w : ℤ) * w i := by
          simp only [dotProduct, mul_sum]
          rw [sum_comm]
          exact sum_congr rfl fun i _ ↦ sum_congr rfl fun w _ ↦ by ring
      _ = 0 := by simp [h]
  have := (sum_eq_zero_iff_of_nonneg fun w hw ↦ mul_nonneg (Nat.cast_nonneg _)
    (hu w (Multiset.mem_toFinset.1 hw))).1 hsum v (Multiset.mem_toFinset.2 hv)
  exact (mul_eq_zero.1 this).resolve_left (Nat.cast_ne_zero.2 (Multiset.count_ne_zero.2 hv))

end General

variable {S : Finset (Fin 4 → SignType)}

/-- A family admits no witness when every integer functional that is nonnegative on it vanishes
on it. -/
private def NoWitness (S : Finset (Fin 4 → SignType)) : Prop :=
  ∀ ⦃u : Fin 4 → ℤ⦄, (∀ v ∈ S, 0 ≤ u ⬝ᵥ fun i ↦ (v i : ℤ)) →
    ∀ ⦃v⦄, v ∈ S → (u ⬝ᵥ fun i ↦ (v i : ℤ)) = 0

private lemma NoWitness.eq_zero (hS : NoWitness S) {u : Fin 4 → ℤ}
    (hu : ∀ v ∈ S, 0 ≤ u ⬝ᵥ fun i ↦ (v i : ℤ)) {v : Fin 4 → SignType} (hv : v ∈ S) :
    (u ⬝ᵥ fun i ↦ (v i : ℤ)) = 0 :=
  hS hu hv

private lemma neg_one_le_mul (a b : SignType) : -1 ≤ (a : ℤ) * b := by
  revert a b; decide

private lemma mul_self_eq_one {a : SignType} (h : a ≠ 0) : (a : ℤ) * a = 1 := by
  revert h; revert a; decide

private lemma exists_eq_of_not_mergeable {v w : Fin 4 → SignType} (h : ¬Mergeable v w) :
    ∃ j s, s ≠ 0 ∧ v j = s ∧ w j = s := by
  rw [Mergeable, not_and_or, Set.not_disjoint_iff, Set.not_disjoint_iff] at h
  rcases h with ⟨j, hv, hw⟩ | ⟨j, hv, hw⟩
  exacts [⟨j, 1, by decide, hv, hw⟩, ⟨j, -1, by decide, hv, hw⟩]

/-! ### At most three members -/

private lemma false_of_subset_triple (hS : NoWitness S) {a b c : Fin 4 → SignType} (ha : a ∈ S)
    (hsub : S ⊆ {a, b, c}) {j₁ j₂ : Fin 4} {s₁ s₂ : SignType} (hs₁ : s₁ ≠ 0) (hs₂ : s₂ ≠ 0)
    (ha₁ : a j₁ = s₁) (hb₁ : b j₁ = s₁) (ha₂ : a j₂ = s₂) (hc₂ : c j₂ = s₂) : False := by
  have hval (v : Fin 4 → SignType) : ((Pi.single j₁ (s₁ : ℤ) + Pi.single j₂ (s₂ : ℤ)) ⬝ᵥ
      fun i ↦ (v i : ℤ)) = s₁ * v j₁ + s₂ * v j₂ := by
    simp [add_dotProduct]
  have h := hS.eq_zero (u := Pi.single j₁ (s₁ : ℤ) + Pi.single j₂ (s₂ : ℤ))
    (fun v hv ↦ ?_) ha
  · rw [hval, ha₁, ha₂, mul_self_eq_one hs₁, mul_self_eq_one hs₂] at h
    omega
  rw [hval]
  have h₁ := neg_one_le_mul s₁ (v j₁)
  have h₂ := neg_one_le_mul s₂ (v j₂)
  rcases (by simpa using hsub hv : v = a ∨ v = b ∨ v = c) with rfl | rfl | rfl
  · rw [ha₁, ha₂, mul_self_eq_one hs₁, mul_self_eq_one hs₂]; omega
  · rw [hb₁, mul_self_eq_one hs₁]; omega
  · rw [hc₂, mul_self_eq_one hs₂]; omega

private lemma false_of_card_le_three (hS : NoWitness S) (hposne : ∀ v ∈ S, ∃ i, v i = 1)
    (hmerge : (S : Set (Fin 4 → SignType)).Pairwise (¬Mergeable · ·)) (hne : S.Nonempty)
    (h3 : #S ≤ 3) : False := by
  rcases (by have := card_pos.2 hne; omega : #S = 1 ∨ #S = 2 ∨ #S = 3) with h | h | h
  · obtain ⟨a, rfl⟩ := card_eq_one.1 h
    obtain ⟨k, hk⟩ := hposne a (mem_singleton_self a)
    exact false_of_subset_triple (b := a) (c := a) hS (mem_singleton_self a) (by simp)
      one_ne_zero one_ne_zero hk hk hk hk
  · obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 h
    obtain ⟨j, s, hs, haj, hbj⟩ :=
      exists_eq_of_not_mergeable (hmerge (by simp) (by simp) hab)
    exact false_of_subset_triple (c := b) hS (by simp) (by simp) hs hs haj hbj haj hbj
  · obtain ⟨a, b, c, hab, hac, -, rfl⟩ := card_eq_three.1 h
    obtain ⟨j₁, s₁, hs₁, ha₁, hb₁⟩ :=
      exists_eq_of_not_mergeable (hmerge (by simp) (by simp) hab)
    obtain ⟨j₂, s₂, hs₂, ha₂, hc₂⟩ :=
      exists_eq_of_not_mergeable (hmerge (by simp) (by simp) hac)
    exact false_of_subset_triple hS (by simp) subset_rfl hs₁ hs₂ ha₁ hb₁ ha₂ hc₂

/-! ### Members have at most one zero coordinate -/

/-- `pos w` is the finset of positive coordinates of `w`. -/
private def pos (w : Fin 4 → SignType) : Finset (Fin 4) := {i | w i = 1}

/-- `neg w` is the finset of negative coordinates of `w`. -/
private def neg (w : Fin 4 → SignType) : Finset (Fin 4) := {i | w i = -1}

@[simp] private lemma mem_pos {w : Fin 4 → SignType} {i : Fin 4} : i ∈ pos w ↔ w i = 1 := by
  simp [pos]

@[simp] private lemma mem_neg {w : Fin 4 → SignType} {i : Fin 4} : i ∈ neg w ↔ w i = -1 := by
  simp [neg]

private lemma coe_pos (w : Fin 4 → SignType) : (pos w : Set (Fin 4)) = posSupport w := by
  ext; simp

private lemma disjoint_pos_neg (w : Fin 4 → SignType) : Disjoint (pos w) (neg w) :=
  disjoint_filter.2 fun i _ h1 h2 ↦ by simp [h1] at h2

private lemma one_dotProduct_eq (w : Fin 4 → SignType) :
    ((1 : Fin 4 → ℤ) ⬝ᵥ fun i ↦ (w i : ℤ)) = #(pos w) - #(neg w) := by
  have key (a : SignType) : (a : ℤ) = (if a = 1 then 1 else 0) - (if a = -1 then 1 else 0) := by
    revert a; decide
  simp only [one_dotProduct, pos, neg, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, ← sum_sub_distrib]
  exact sum_congr rfl fun i _ ↦ key (w i)

private lemma card_pos_add_card_neg_le (w : Fin 4 → SignType) {z : Fin 4} (hz : w z = 0) :
    #(pos w) + #(neg w) ≤ 3 := by
  rw [← card_union_of_disjoint (disjoint_pos_neg w)]
  calc #(pos w ∪ neg w) ≤ #(univ.erase z) := card_le_card fun k hk ↦ mem_erase.2
        ⟨by rintro rfl; simp [hz] at hk, mem_univ k⟩
    _ = 3 := by rw [card_erase_of_mem (mem_univ z), card_univ, Fintype.card_fin]

private lemma card_pos_add_card_neg_le_four (w : Fin 4 → SignType) : #(pos w) + #(neg w) ≤ 4 := by
  rw [← card_union_of_disjoint (disjoint_pos_neg w)]
  exact (card_le_univ _).trans_eq (Fintype.card_fin 4)

private lemma at_most_one_zero (hS : NoWitness S) (hposne : ∀ v ∈ S, ∃ i, v i = 1)
    (hmerge : (S : Set (Fin 4 → SignType)).Pairwise (¬Mergeable · ·))
    {v : Fin 4 → SignType} (hvS : v ∈ S) {i₁ i₂ : Fin 4} (hne : i₁ ≠ i₂)
    (hz1 : v i₁ = 0) (hz2 : v i₂ = 0) : False := by
  set supp : Finset (Fin 4) := {i | v i ≠ 0} with hsupp
  have hsupp_card : #supp ≤ 2 := by
    have hsub : supp ⊆ univ \ {i₁, i₂} := fun i hi ↦ by
      simp only [hsupp, mem_filter, mem_univ, true_and] at hi
      simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, true_and]
      rintro (rfl | rfl) <;> contradiction
    calc #supp ≤ #(univ \ {i₁, i₂}) := card_le_card hsub
      _ = 2 := by rw [card_univ_sdiff, card_pair hne, Fintype.card_fin]
  set u : Fin 4 → ℤ := fun i ↦ v i with hu
  have hge : ∀ w ∈ S, 0 ≤ u ⬝ᵥ fun i ↦ (w i : ℤ) := by
    intro w hwS
    rcases eq_or_ne w v with rfl | hwv
    · exact sum_nonneg fun i _ ↦ mul_self_nonneg _
    -- a shared sign contributes `1`, and `supp` has at most one other coordinate
    obtain ⟨j, s, hs, hvj, hwj⟩ := exists_eq_of_not_mergeable (hmerge hvS hwS hwv.symm)
    have hjsupp : j ∈ supp := by simp [hsupp, hvj, hs]
    have hip_supp : (u ⬝ᵥ fun i ↦ (w i : ℤ)) = ∑ i ∈ supp, u i * w i := by
      refine (sum_filter_of_ne fun i _ hne0 ↦ ?_).symm
      intro h0
      exact hne0 (by simp [hu, h0])
    have hbound : ∀ i ∈ supp.erase j, -1 ≤ u i * w i := fun i _ ↦ neg_one_le_mul _ _
    have hsum_erase : -#(supp.erase j) ≤ ∑ i ∈ supp.erase j, u i * w i := by
      simpa using card_nsmul_le_sum _ _ _ hbound
    have hcard_erase : #(supp.erase j) ≤ 1 := by rw [card_erase_of_mem hjsupp]; omega
    have hj1 : u j * (w j : ℤ) = 1 := by simp only [hu, hvj, hwj]; exact mul_self_eq_one hs
    rw [hip_supp, ← add_sum_erase _ _ hjsupp, hj1]
    omega
  obtain ⟨k, hk⟩ := hposne v hvS
  have h := hS.eq_zero hge hvS
  have : 1 ≤ u ⬝ᵥ fun i ↦ (v i : ℤ) :=
    calc (1 : ℤ) = u k * v k := by simp [hu, hk]
      _ ≤ ∑ i, u i * v i := single_le_sum (fun i _ ↦ mul_self_nonneg (u i)) (mem_univ k)
  omega

/-! ### The weight-3 singleton-positive kill

A singleton-positive weight-3 member `x` (one `+1`, one `0`, two `-1`s) forces,
via the functional `e_p + e_ζ`, an *s-shape* companion `y₁` (zero at `x`'s
positive coordinate, `-1` at `x`'s zero); `y₁` is again singleton-positive
weight-3, so the forcing iterates.  Pairwise admissibility kills one branch of
the second iterate, pinning the 3-cycle `x, y₁, y₂`, whose witness
`e_p + e_i + e_ζ - e_j` is nonnegative on every admissible sign pattern
and positive at `x`, contradicting balance. -/

private lemma fin4_exhaust : ∀ p ζ i j k : Fin 4, p ≠ ζ → i ≠ p → i ≠ ζ →
    j ≠ p → j ≠ ζ → i ≠ j → k = p ∨ k = ζ ∨ k = i ∨ k = j := by
  decide

private lemma exists_fourth : ∀ p ζ i : Fin 4, p ≠ ζ → i ≠ p → i ≠ ζ →
    ∃ j, j ≠ p ∧ j ≠ ζ ∧ j ≠ i := by
  decide

private lemma posSupport_eq_singleton {x : Fin 4 → SignType} {p ζ : Fin 4}
    (hxp : x p = 1) (hxζ : x ζ = 0) (hxn : ∀ k, k ≠ p → k ≠ ζ → x k = -1) :
    posSupport x = {p} := by
  ext k
  simp only [mem_posSupport, Set.mem_singleton_iff]
  refine ⟨fun hk ↦ by_contra fun hkp ↦ ?_, by rintro rfl; exact hxp⟩
  rcases eq_or_ne k ζ with rfl | hkζ
  · simp [hxζ] at hk
  · simp [hxn k hkp hkζ] at hk

private lemma negSupport_eq_pair {x : Fin 4 → SignType} {p ζ i j : Fin 4}
    (hpζ : p ≠ ζ) (hip : i ≠ p) (hiζ : i ≠ ζ) (hjp : j ≠ p) (hjζ : j ≠ ζ)
    (hij : i ≠ j) (hxp : x p = 1) (hxζ : x ζ = 0)
    (hxn : ∀ k, k ≠ p → k ≠ ζ → x k = -1) :
    negSupport x = {i, j} := by
  ext k
  simp only [mem_negSupport, Set.mem_insert_iff, Set.mem_singleton_iff]
  refine ⟨fun hk ↦ ?_, by rintro (rfl | rfl) <;> apply hxn <;> assumption⟩
  rcases fin4_exhaust p ζ i j k hpζ hip hiζ hjp hjζ hij with rfl | rfl | rfl | rfl
  · simp [hxp] at hk
  · simp [hxζ] at hk
  · exact .inl rfl
  · exact .inr rfl

private lemma constraints_of_sp3 (hmerge : (S : Set (Fin 4 → SignType)).Pairwise (¬Mergeable · ·))
    (hno : (S : Set (Fin 4 → SignType)).Pairwise (¬AntiDominating · ·))
    {x w : Fin 4 → SignType} (hxS : x ∈ S) (hwS : w ∈ S) (hxw : x ≠ w)
    {p ζ i j : Fin 4} (hpζ : p ≠ ζ) (hip : i ≠ p) (hiζ : i ≠ ζ)
    (hjp : j ≠ p) (hjζ : j ≠ ζ) (hij : i ≠ j)
    (hxp : x p = 1) (hxζ : x ζ = 0) (hxn : ∀ k, k ≠ p → k ≠ ζ → x k = -1) :
    (w p = 1 ∨ w i = -1 ∨ w j = -1) ∧ (w p ≠ -1 ∨ w ζ = 1) := by
  have hsx := posSupport_eq_singleton hxp hxζ hxn
  have hnx := negSupport_eq_pair hpζ hip hiζ hjp hjζ hij hxp hxζ hxn
  constructor
  · by_contra hc
    push Not at hc
    obtain ⟨h1, h2, h3⟩ := hc
    refine hmerge hxS hwS hxw ⟨?_, ?_⟩
    · rw [hsx, Set.disjoint_singleton_left]; exact h1
    · rw [hnx, Set.disjoint_insert_left, Set.disjoint_singleton_left]; exact ⟨h2, h3⟩
  · by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    refine hno hxS hwS hxw ⟨by rw [hsx, Set.singleton_subset_iff]; exact h1, fun k hk ↦ ?_⟩
    rw [hnx]
    rcases fin4_exhaust p ζ i j k hpζ hip hiζ hjp hjζ hij with rfl | rfl | rfl | rfl
    · simp [mem_posSupport.1 hk] at h1
    · exact absurd hk h2
    · exact .inl rfl
    · exact .inr rfl

private lemma wt3_witness_bound (wp wi wj wz : SignType)
    (h1 : wp = 1 ∨ wi = 1 ∨ wj = 1 ∨ wz = 1)
    (h2p : wp = 0 → wi ≠ 0 ∧ wj ≠ 0 ∧ wz ≠ 0)
    (h2i : wi = 0 → wj ≠ 0 ∧ wz ≠ 0)
    (h2j : wj = 0 → wz ≠ 0)
    (hgx : wp = 1 ∨ wi = -1 ∨ wj = -1)
    (hax : wp ≠ -1 ∨ wz = 1)
    (hgy1 : wi = 1 ∨ wj = -1 ∨ wz = -1)
    (hay1 : wi ≠ -1 ∨ wp = 1)
    (hgy2 : wz = 1 ∨ wp = -1 ∨ wj = -1)
    (hay2 : wz ≠ -1 ∨ wi = 1) :
    0 ≤ (wp : ℤ) + wi + wz - wj := by
  cases wp <;> cases wi <;> cases wj <;> cases wz <;> simp_all +decide

private lemma s_shape_forcing (hS : NoWitness S) (hposne : ∀ v ∈ S, ∃ i, v i = 1)
    (hmerge : (S : Set (Fin 4 → SignType)).Pairwise (¬Mergeable · ·))
    (hno : (S : Set (Fin 4 → SignType)).Pairwise (¬AntiDominating · ·))
    {x : Fin 4 → SignType} (hxS : x ∈ S) {p ζ : Fin 4} (hpζ : p ≠ ζ)
    (hxp : x p = 1) (hxζ : x ζ = 0) (hxn : ∀ k, k ≠ p → k ≠ ζ → x k = -1) :
    ∃ y ∈ S, ∃ i j : Fin 4, i ≠ p ∧ i ≠ ζ ∧ j ≠ p ∧ j ≠ ζ ∧ i ≠ j ∧
      y p = 0 ∧ y ζ = -1 ∧ y i = 1 ∧ y j = -1 := by
  have hsx := posSupport_eq_singleton hxp hxζ hxn
  -- the functional `e_p + e_ζ` is `1` at `x`, so it is negative on some member `y`
  obtain ⟨y, hyS, hy⟩ : ∃ y ∈ S, (y p : ℤ) + y ζ < 0 := by
    by_contra! hall
    have h := hS.eq_zero (u := Pi.single p 1 + Pi.single ζ 1)
      (fun w hw ↦ by simpa [add_dotProduct] using hall w hw) hxS
    simp [add_dotProduct, hxp, hxζ] at h
  have hxy : x ≠ y := by rintro rfl; simp [hxp, hxζ] at hy
  -- pin the shape of `y`: `y p = 0` and `y ζ = -1`
  have hyp : y p = 0 := by
    rcases (y p).trichotomy with h | h | h
    · -- `y p = -1` forces `y ζ = 1` by non-anti-domination, making the value `0`
      exfalso
      have hsub : posSupport x ⊆ negSupport y := by
        rw [hsx, Set.singleton_subset_iff]; exact h
      obtain ⟨m, hmy, hmx⟩ := Set.not_subset.1 fun h' ↦ hno hxS hyS hxy ⟨hsub, h'⟩
      rw [mem_posSupport] at hmy
      rw [mem_negSupport] at hmx
      have hmp : m ≠ p := by rintro rfl; simp [h] at hmy
      obtain rfl : m = ζ := by_contra fun hmζ ↦ hmx (hxn m hmp hmζ)
      simp [h, hmy] at hy
    · exact h
    · exfalso
      rcases (y ζ).trichotomy with h' | h' | h' <;> simp [h, h'] at hy
  have hyζ : y ζ = -1 := by
    rcases (y ζ).trichotomy with h | h | h
    · exact h
    all_goals simp [hyp, h] at hy
  -- `y`'s positive coordinate is off `{p, ζ}`
  obtain ⟨i, hyi⟩ := hposne y hyS
  have hip : i ≠ p := by rintro rfl; simp [hyp] at hyi
  have hiζ : i ≠ ζ := by rintro rfl; simp [hyζ] at hyi
  -- the fourth coordinate carries `-1`, by non-mergeability with `x`
  obtain ⟨j, hjp, hjζ, hji⟩ := exists_fourth p ζ i hpζ hip hiζ
  have hyj : y j = -1 := by
    have hdp : Disjoint (posSupport x) (posSupport y) := by
      rw [hsx, Set.disjoint_singleton_left, mem_posSupport, hyp]; decide
    obtain ⟨m, hmx, hmy⟩ := Set.not_disjoint_iff.1 fun hdn ↦ hmerge hxS hyS hxy ⟨hdp, hdn⟩
    rw [mem_negSupport] at hmx hmy
    rcases fin4_exhaust p ζ i j m hpζ hip hiζ hjp hjζ (Ne.symm hji) with rfl | rfl | rfl | rfl
    · simp [hxp] at hmx
    · simp [hxζ] at hmx
    · simp [hyi] at hmy
    · exact hmy
  exact ⟨y, hyS, i, j, hip, hiζ, hjp, hjζ, Ne.symm hji, hyp, hyζ, hyi, hyj⟩

private lemma sp3_kill (hS : NoWitness S) (hposne : ∀ v ∈ S, ∃ i, v i = 1)
    (hmerge : (S : Set (Fin 4 → SignType)).Pairwise (¬Mergeable · ·))
    (hno : (S : Set (Fin 4 → SignType)).Pairwise (¬AntiDominating · ·))
    {x : Fin 4 → SignType} (hxS : x ∈ S) {p ζ : Fin 4} (hpζ : p ≠ ζ)
    (hxp : x p = 1) (hxζ : x ζ = 0) (hxn : ∀ k, k ≠ p → k ≠ ζ → x k = -1) : False := by
  obtain ⟨y₁, hy₁S, i, j, hip, hiζ, hjp, hjζ, hij, hy₁p, hy₁ζ, hy₁i, hy₁j⟩ :=
    s_shape_forcing hS hposne hmerge hno hxS hpζ hxp hxζ hxn
  -- `y₁` is singleton-positive weight-3 with roles (pos `i`, zero `p`, negs `{j, ζ}`)
  have hy₁n : ∀ k, k ≠ i → k ≠ p → y₁ k = -1 := by
    intro k hki hkp
    rcases fin4_exhaust p ζ i j k hpζ hip hiζ hjp hjζ hij with rfl | rfl | rfl | rfl
    · exact absurd rfl hkp
    · exact hy₁ζ
    · exact absurd rfl hki
    · exact hy₁j
  obtain ⟨y₂, hy₂S, a, b, hai, hap, hbi, hbp, hab, hy₂i, hy₂p, hy₂a, hy₂b⟩ :=
    s_shape_forcing hS hposne hmerge hno hy₁S hip hy₁i hy₁p hy₁n
  -- `a` and `b` land in `{ζ, j}`
  have ha : a = ζ ∨ a = j := by
    rcases fin4_exhaust p ζ i j a hpζ hip hiζ hjp hjζ hij with rfl | rfl | rfl | rfl
    · exact absurd rfl hap
    · exact Or.inl rfl
    · exact absurd rfl hai
    · exact Or.inr rfl
  have hb : b = ζ ∨ b = j := by
    rcases fin4_exhaust p ζ i j b hpζ hip hiζ hjp hjζ hij with rfl | rfl | rfl | rfl
    · exact absurd rfl hbp
    · exact Or.inl rfl
    · exact absurd rfl hbi
    · exact Or.inr rfl
  rcases ha with rfl | rfl
  · -- `a = ζ`: live 3-cycle; pin `b = j`
    rcases hb with rfl | rfl
    · exact hab rfl
    -- `y₂`'s remaining structure
    have hy₂n : ∀ k, k ≠ a → k ≠ i → y₂ k = -1 := by
      intro k hkζ hki
      rcases fin4_exhaust p a i b k hpζ hip hiζ hjp hjζ hij with rfl | rfl | rfl | rfl
      · exact hy₂p
      · exact absurd rfl hkζ
      · exact absurd rfl hki
      · exact hy₂b
    -- the witness `e_p + e_i + e_a - e_b` is nonnegative on the family
    have hterm : ∀ w ∈ S, 0 ≤ (w p : ℤ) + w i + w a - w b := by
      intro w hw
      rcases eq_or_ne w x with rfl | hwx
      · simp [hxp, hxζ, hxn i hip hiζ, hxn b hjp hjζ]
      rcases eq_or_ne w y₁ with rfl | hwy₁
      · simp [hy₁p, hy₁ζ, hy₁i, hy₁j]
      rcases eq_or_ne w y₂ with rfl | hwy₂
      · simp [hy₂p, hy₂i, hy₂a, hy₂b]
      -- otherwise: translate the pair constraints and close by sign arithmetic
      have hpos1 : w p = 1 ∨ w i = 1 ∨ w b = 1 ∨ w a = 1 := by
        obtain ⟨k, hk⟩ := hposne w hw
        rcases fin4_exhaust p a i b k hpζ hip hiζ hjp hjζ hij with rfl | rfl | rfl | rfl
        · exact Or.inl hk
        · exact Or.inr (Or.inr (Or.inr hk))
        · exact Or.inr (Or.inl hk)
        · exact Or.inr (Or.inr (Or.inl hk))
      have hamoz : ∀ {k₁ k₂ : Fin 4}, k₁ ≠ k₂ → w k₁ = 0 → w k₂ ≠ 0 :=
        fun hne hz1 hz2 ↦ at_most_one_zero hS hposne hmerge hw hne hz1 hz2
      have h2p : w p = 0 → w i ≠ 0 ∧ w b ≠ 0 ∧ w a ≠ 0 := fun hz ↦
        ⟨hamoz (Ne.symm hip) hz, hamoz (Ne.symm hjp) hz, hamoz hpζ hz⟩
      have h2i : w i = 0 → w b ≠ 0 ∧ w a ≠ 0 := fun hz ↦ ⟨hamoz hij hz, hamoz hiζ hz⟩
      have h2j : w b = 0 → w a ≠ 0 := fun hz ↦ hamoz hjζ hz
      obtain ⟨hgx, hax⟩ := constraints_of_sp3 hmerge hno hxS hw (Ne.symm hwx)
        hpζ hip hiζ hjp hjζ hij hxp hxζ hxn
      obtain ⟨hgy1, hay1⟩ := constraints_of_sp3 hmerge hno hy₁S hw (Ne.symm hwy₁)
        hip (Ne.symm hij) hjp (Ne.symm hiζ) (Ne.symm hpζ) hjζ hy₁i hy₁p hy₁n
      obtain ⟨hgy2, hay2⟩ := constraints_of_sp3 hmerge hno hy₂S hw (Ne.symm hwy₂)
        (Ne.symm hiζ) hpζ (Ne.symm hip) hjζ (Ne.symm hij) (Ne.symm hjp) hy₂a hy₂i hy₂n
      exact wt3_witness_bound (w p) (w i) (w b) (w a) hpos1 h2p h2i h2j hgx hax hgy1 hay1
        hgy2 hay2
    have h := hS.eq_zero
      (u := Pi.single p 1 + Pi.single i 1 + Pi.single a 1 - Pi.single b 1)
      (fun w hw ↦ by simpa [add_dotProduct, sub_dotProduct] using hterm w hw) hxS
    simp [add_dotProduct, sub_dotProduct, hxp, hxζ, hxn i hip hiζ, hxn b hjp hjζ] at h
  · -- `a = j`: `y₂` merges with `x`, a contradiction
    have hxy₂ : x ≠ y₂ := by rintro rfl; simp [hxp] at hy₂p
    rcases hb with rfl | rfl
    · -- `b = ζ`: `y₂ = (-1@p, 0@i, +1@j, -1@ζ)`
      refine hmerge hxS hy₂S hxy₂ ⟨?_, ?_⟩
      · rw [posSupport_eq_singleton hxp hxζ hxn, Set.disjoint_singleton_left, mem_posSupport,
          hy₂p]
        decide
      · rw [negSupport_eq_pair hpζ hip hiζ hjp hjζ hij hxp hxζ hxn, Set.disjoint_insert_left,
          Set.disjoint_singleton_left, mem_negSupport, mem_negSupport, hy₂i, hy₂a]
        decide
    · exact hab rfl

/-! ### Four or more members -/

/-- The six 2-element subsets of `Fin 4` split into three complementary pairs;
    `pairClass` names the pair. -/
private def pairClass (P : Finset (Fin 4)) : Fin 3 :=
  if P = {0, 1} ∨ P = {2, 3} then 0 else if P = {0, 2} ∨ P = {1, 3} then 1 else 2

private lemma pairClass_eq_disjoint : ∀ P Q : Finset (Fin 4),
    #P = 2 → #Q = 2 → P ≠ Q → pairClass P = pairClass Q → P ∩ Q = ∅ := by
  decide

private lemma antiDominating_of_ne_zero {v w : Fin 4 → SignType} (hv : ∀ i, v i ≠ 0)
    (hw : ∀ i, w i ≠ 0) (hdisj : Disjoint (posSupport v) (posSupport w)) :
    AntiDominating v w := by
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · rcases (w i).trichotomy with h | h | h
    exacts [h, absurd h (hw i), absurd h (Set.disjoint_left.1 hdisj hi)]
  · rcases (v i).trichotomy with h | h | h
    exacts [h, absurd h (hv i), absurd hi (Set.disjoint_left.1 hdisj h)]

private lemma false_of_four_le_card (hS : NoWitness S) (hposne : ∀ v ∈ S, ∃ i, v i = 1)
    (hmerge : (S : Set (Fin 4 → SignType)).Pairwise (¬Mergeable · ·))
    (hno : (S : Set (Fin 4 → SignType)).Pairwise (¬AntiDominating · ·)) (h4 : 4 ≤ #S) :
    False := by
  -- every member has at least two positive coordinates
  have hcard2 : ∀ v ∈ S, 2 ≤ #(pos v) := by
    intro v hv
    by_contra! hlt
    obtain ⟨k, hk⟩ := hposne v hv
    have hk' : posSupport v = {k} := by
      rw [← coe_pos, ← coe_singleton, coe_inj]
      exact eq_singleton_iff_unique_mem.2
        ⟨mem_pos.2 hk, fun x hx ↦ card_le_one.1 (by omega) x hx k (mem_pos.2 hk)⟩
    by_cases hzero : ∃ m, v m = 0
    · -- weight 3: the s-shape chain
      obtain ⟨m, hm⟩ := hzero
      have hmk : k ≠ m := by rintro rfl; simp [hk] at hm
      have hvn : ∀ l, l ≠ k → l ≠ m → v l = -1 := by
        intro l hlk hlm
        rcases (v l).trichotomy with h | h | h
        · exact h
        · exact (at_most_one_zero hS hposne hmerge hv hlm h hm).elim
        · exact absurd (by rw [← Set.mem_singleton_iff, ← hk']; exact h) hlk
      exact sp3_kill hS hposne hmerge hno hv hmk hk hm hvn
    -- full support: `e_k` is nonnegative on the family and `1` at `v`
    push Not at hzero
    have hnok : ∀ w ∈ S, 0 ≤ (w k : ℤ) := by
      intro w hw
      rcases eq_or_ne w v with rfl | hwv
      · simp [hk]
      rcases (w k).trichotomy with h | h | h
      · -- `pos v = {k} ⊆ neg w`, so some positive coordinate of `w` is positive in `v`
        have hsub : posSupport v ⊆ negSupport w := by
          rw [hk', Set.singleton_subset_iff]; exact h
        obtain ⟨m, hmw, hmv⟩ := Set.not_subset.1 fun h' ↦ hno hv hw hwv.symm ⟨hsub, h'⟩
        rw [mem_posSupport] at hmw
        rw [mem_negSupport] at hmv
        have hm1 : v m = 1 := by
          rcases (v m).trichotomy with h' | h' | h'
          exacts [absurd h' hmv, absurd h' (hzero m), h']
        obtain rfl : m = k := by rw [← Set.mem_singleton_iff, ← hk']; exact hm1
        simp [hmw] at h
      all_goals simp [h]
    have h := hS.eq_zero (u := Pi.single k 1) (fun w hw ↦ by simpa using hnok w hw) hv
    simp [hk] at h
  -- `𝟙` is then nonnegative on the family, so every member has two coordinates of each sign
  have hnn : ∀ w ∈ S, 0 ≤ (1 : Fin 4 → ℤ) ⬝ᵥ fun i ↦ (w i : ℤ) := fun w hw ↦ by
    rw [one_dotProduct_eq]
    have := hcard2 w hw
    have := card_pos_add_card_neg_le_four w
    omega
  have hfull : ∀ w ∈ S, #(pos w) = 2 ∧ ∀ i, w i ≠ 0 := by
    intro w hw
    have h0 := hS.eq_zero hnn hw
    rw [one_dotProduct_eq] at h0
    have := hcard2 w hw
    have := card_pos_add_card_neg_le_four w
    refine ⟨by omega, fun z hz ↦ ?_⟩
    have := card_pos_add_card_neg_le w hz
    omega
  have hinj : ∀ v ∈ S, ∀ w ∈ S, pos v = pos w → v = w := by
    intro v hv w hw heq
    funext i
    have h := congrArg (i ∈ ·) heq
    simp only [mem_pos, eq_iff_iff] at h
    have := (hfull v hv).2 i
    have := (hfull w hw).2 i
    rcases (v i).trichotomy with h1 | h1 | h1 <;> rcases (w i).trichotomy with h2 | h2 | h2 <;>
      simp_all
  -- pigeonhole: four distinct 2-subsets land in three complement classes
  obtain ⟨T, hTS, hT⟩ := exists_subset_card_eq h4
  obtain ⟨x, hxT, y, hyT, hxy, hpc⟩ := exists_ne_map_eq_of_card_lt_of_maps_to
    (s := T) (t := (univ : Finset (Fin 3))) (f := fun w ↦ pairClass (pos w))
    (by simp [hT]) fun w _ ↦ mem_coe.2 (mem_univ _)
  have hxS : x ∈ S := hTS hxT
  have hyS : y ∈ S := hTS hyT
  have hdisj := pairClass_eq_disjoint _ _ (hfull x hxS).1 (hfull y hyS).1
    (fun h ↦ hxy (hinj _ hxS _ hyS h)) hpc
  refine hno hxS hyS hxy (antiDominating_of_ne_zero (hfull x hxS).2 (hfull y hyS).2 ?_)
  rw [← coe_pos, ← coe_pos, disjoint_coe]
  exact disjoint_iff_inter_eq_empty.2 hdisj

/-- **Anti-domination from balance.** A nonempty multiset of pairwise non-mergeable comparisons
on four atoms, each with a nonempty positive side, that sums to zero contains an anti-dominating
pair. -/
theorem exists_antiDominating {M : Multiset (Fin 4 → SignType)} (hM : comparisonSum M = 0)
    (hpos : ∀ v ∈ M, (posSupport v).Nonempty)
    (hmerge : ∀ v ∈ M, ∀ w ∈ M, v ≠ w → ¬Mergeable v w) (hne : M ≠ 0) :
    ∃ v ∈ M, ∃ w ∈ M, v ≠ w ∧ AntiDominating v w := by
  classical
  have hS : NoWitness M.toFinset := fun u hu v hv ↦
    dotProduct_eq_zero_of_comparisonSum_eq_zero hM
      (fun w hw ↦ hu w (Multiset.mem_toFinset.2 hw)) (Multiset.mem_toFinset.1 hv)
  have hposne : ∀ v ∈ M.toFinset, ∃ i, v i = 1 := fun v hv ↦ hpos v (Multiset.mem_toFinset.1 hv)
  have hmerge' : (M.toFinset : Set (Fin 4 → SignType)).Pairwise (¬Mergeable · ·) :=
    fun v hv w hw ↦ hmerge v (by simpa using hv) w (by simpa using hw)
  by_contra! hno
  rcases le_or_gt #M.toFinset 3 with h | h
  · exact false_of_card_le_three hS hposne hmerge' (Multiset.toFinset_nonempty.2 hne) h
  · exact false_of_four_le_card hS hposne hmerge'
      (fun v hv w hw ↦ hno v (by simpa using hv) w (by simpa using hw)) h

end ComparativeProbability
