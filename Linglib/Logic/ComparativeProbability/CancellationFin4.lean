module

public import Linglib.Logic.ComparativeProbability.Scott
public import Linglib.Logic.ComparativeProbability.SignVectors

/-! # Cancellation on at most four atoms

This file proves that every qualitative probability on at most four atoms satisfies Scott
cancellation, hence is representable by a probability measure. Kraft, Pratt and Seidenberg remark,
without proof, that five atoms are the fewest on which this can fail.

## Main statements

* `ComparativeProbability.no_null_cancellation`: cancellation on at most four atoms, none null.
* `ComparativeProbability.cancellation_of_le_four`: cancellation on at most four atoms.

## Implementation notes

Comparisons are sign vectors. Two comparisons with no shared nonzero coordinate *merge* into the
sign of their sum, again a valid comparison. With no null atom, a valid family whose sum is a
single sign vector proves that comparison by merging recursively. When no pair merges,
`exists_antiDominating` yields either a pair of members that forces a null atom or a member that
merges with the reversed target and is peeled off. A null atom drops out by
`cancellation_of_null_atom`, so one induction covers every size up to four.

## References

* [kraft-pratt-seidenberg-1959]
-/

@[expose] public section

namespace ComparativeProbability

/-! ### Merging comparisons

Two sign vectors are *mergeable* when no coordinate carries the same nonzero
sign in both; their merge is the sign of their sum, which is then their sum. -/

/-- The merge of two sign vectors is the sign of their pointwise sum. -/
private def merge {n : ℕ} (v w : Fin n → SignType) (i : Fin n) : SignType :=
  SignType.sign ((v i : ℤ) + w i)

private lemma merge_apply_aux (a b : SignType) (h : a = b → a = 0) :
    (SignType.sign ((a : ℤ) + b) : ℤ) = a + b := by decide +revert

private lemma sign_add_eq_one_iff (a b : SignType) (h : a = b → a = 0) :
    SignType.sign ((a : ℤ) + b) = 1 ↔ (a = 1 ∨ b = 1) ∧ ¬(a = -1 ∨ b = -1) := by decide +revert

private lemma sign_add_eq_neg_one_iff (a b : SignType) (h : a = b → a = 0) :
    SignType.sign ((a : ℤ) + b) = -1 ↔ (a = -1 ∨ b = -1) ∧ ¬(a = 1 ∨ b = 1) := by decide +revert

private lemma eq_neg_one_of_add_nonpos (a b : SignType) (ha : a = 1) (h : (a : ℤ) + b ≤ 0) :
    b = -1 := by decide +revert

private lemma or_of_add_neg (a b : SignType) (h : (a : ℤ) + b < 0) :
    (a = -1 ∧ ¬b = 1) ∨ (b = -1 ∧ ¬a = 1) := by decide +revert

private lemma add_self_nonpos (a : SignType) (h : a ≠ 1) : (a : ℤ) + a ≤ 0 := by decide +revert

private lemma eq_zero_of_ne_one_of_ne_neg_one (a : SignType) (h₁ : a ≠ 1) (h₂ : a ≠ -1) :
    a = 0 := by decide +revert

private lemma coe_merge {n : ℕ} {v w : Fin n → SignType} (h : Mergeable v w) (i : Fin n) :
    (merge v w i : ℤ) = v i + w i :=
  merge_apply_aux _ _ (mergeable_iff.mp h i)

private lemma posSupport_merge {n : ℕ} {v w : Fin n → SignType} (h : Mergeable v w) :
    posSupport (merge v w) = (posSupport v ∪ posSupport w) \ (negSupport v ∪ negSupport w) := by
  ext i
  simp only [mem_posSupport, merge, Set.mem_sdiff, Set.mem_union, mem_negSupport]
  exact sign_add_eq_one_iff _ _ (mergeable_iff.mp h i)

private lemma negSupport_merge {n : ℕ} {v w : Fin n → SignType} (h : Mergeable v w) :
    negSupport (merge v w) = (negSupport v ∪ negSupport w) \ (posSupport v ∪ posSupport w) := by
  ext i
  simp only [mem_negSupport, merge, Set.mem_sdiff, Set.mem_union, mem_posSupport]
  exact sign_add_eq_neg_one_iff _ _ (mergeable_iff.mp h i)

variable {n : ℕ} {r : Set (Fin n) → Set (Fin n) → Prop}

private lemma merge_valid [IsQualitativeProbability r] {v w : Fin n → SignType}
    (hv : r (posSupport v) (negSupport v)) (hw : r (posSupport w) (negSupport w))
    (h : Mergeable v w) : r (posSupport (merge v w)) (negSupport (merge v w)) := by
  have hmerge := rel_sup_sup hv hw h.1 h.2
  rw [qadd (r := r)] at hmerge
  rwa [posSupport_merge h, negSupport_merge h]

private lemma null_from_pair [IsQualitativeProbability r] {v w : Fin n → SignType}
    (hv : r (posSupport v) (negSupport v)) (hw : r (posSupport w) (negSupport w))
    (hle : ∀ i, (v i : ℤ) + w i ≤ 0) (i₀ : Fin n) (hlt : (v i₀ : ℤ) + w i₀ < 0) :
    ∃ i, r ∅ {i} := by
  have hpn : ∀ i, v i = 1 → w i = -1 := fun i h ↦ eq_neg_one_of_add_nonpos _ _ h (hle i)
  have hpn' : ∀ i, w i = 1 → v i = -1 := fun i h ↦
    eq_neg_one_of_add_nonpos _ _ h (by rw [add_comm]; exact hle i)
  have hAD : posSupport v ⊆ negSupport w := fun i h ↦ hpn i h
  have hCB : posSupport w ⊆ negSupport v := fun i h ↦ hpn' i h
  -- `pos w ≿ pos v` and `pos w ≿ neg v`
  have hCA : r (posSupport w) (posSupport v) := trans_of r hw (mono _ _ hAD)
  have hCB_ge : r (posSupport w) (negSupport v) := trans_of r hCA hv
  have hBC : r ∅ (negSupport v \ posSupport w) := by
    have hax := (qadd (r := r) _ _).mp hCB_ge
    rwa [Set.sdiff_eq_empty.mpr hCB] at hax
  have hAC : r (posSupport v) (posSupport w) := trans_of r hv (mono _ _ hCB)
  have hDA : r ∅ (negSupport w \ posSupport v) := by
    have hax := (qadd (r := r) _ _).mp (trans_of r hAC hw)
    rwa [Set.sdiff_eq_empty.mpr hAD] at hax
  have hmem : i₀ ∈ negSupport v \ posSupport w ∨ i₀ ∈ negSupport w \ posSupport v := by
    simp only [Set.mem_sdiff, mem_negSupport, mem_posSupport]
    exact or_of_add_neg _ _ hlt
  rcases hmem with hm | hm
  · exact ⟨i₀, trans_of r hBC (mono _ _ (Set.singleton_subset_iff.mpr hm))⟩
  · exact ⟨i₀, trans_of r hDA (mono _ _ (Set.singleton_subset_iff.mpr hm))⟩

/-! ### The stuck case of the merge recursion -/

private lemma add_nonpos_of_imp (a b : SignType) (h₁ : a = 1 → b = -1) (h₂ : b = 1 → a = -1) :
    (a : ℤ) + b ≤ 0 := by decide +revert

private lemma eq_zero_of_add_eq_zero_of_eq (a b : SignType) (h : (a : ℤ) + b = 0) (hab : a = b) :
    a = 0 := by decide +revert

private lemma comparisonSum_filter_ne_zero {n : ℕ} (M : Multiset (Fin n → SignType)) (i : Fin n) :
    comparisonSum (M.filter (· ≠ 0)) i = comparisonSum M i := by
  induction M using Multiset.induction_on with
  | empty => rfl
  | cons v M ih =>
    by_cases hv : v = 0
    · rw [Multiset.filter_cons_of_neg _ (by simpa using hv), comparisonSum_cons, ih, hv]; simp
    · rw [Multiset.filter_cons_of_pos _ (by simpa using hv), comparisonSum_cons,
        comparisonSum_cons, ih]

private lemma v1_tailored (hn : n ≤ 4) (M : Multiset (Fin n → SignType)) {t : Fin n → SignType}
    (hsum : ∀ i, comparisonSum M i = t i) (hne : (negSupport t).Nonempty)
    (hnotdom : ∀ v ∈ M, posSupport v ⊆ posSupport t → ¬ negSupport t ⊆ negSupport v)
    (hnogm : ¬ ∃ v w rest, M = v ::ₘ w ::ₘ rest ∧ Mergeable v w) :
    (∃ v ∈ M, ∃ w ∈ M, (∀ i, (v i : ℤ) + w i ≤ 0) ∧ ∃ i, (v i : ℤ) + w i < 0)
      ∨ ∃ v ∈ M, Mergeable (-t) v := by
  classical
  -- Step A: a member with empty positive support and nonempty negative support
  -- is a null pair with itself
  by_cases hemp : ∃ v ∈ M, posSupport v = ∅ ∧ (negSupport v).Nonempty
  · obtain ⟨v, hvL, hv1, k, hk⟩ := hemp
    have hv0 : ∀ i, v i ≠ 1 := fun i h ↦ Set.notMem_empty i (hv1 ▸ h)
    refine Or.inl ⟨v, hvL, v, hvL, fun i ↦ add_self_nonpos _ (hv0 i), k, ?_⟩
    rw [mem_negSupport.mp hk]; decide
  -- Step B: the right disjunct as an escape hatch
  by_cases hrd : ∃ v ∈ M, Mergeable (-t) v
  · exact Or.inr hrd
  have h0 : ∀ v ∈ M, v ≠ 0 → (posSupport v).Nonempty := by
    intro v hv hv0
    by_contra h1
    rw [Set.not_nonempty_iff_eq_empty] at h1
    have h2 : negSupport v = ∅ := by
      by_contra h2
      exact hemp ⟨v, hv, h1, Set.nonempty_iff_ne_empty.mpr h2⟩
    refine hv0 (funext fun i ↦ eq_zero_of_ne_one_of_ne_neg_one _ ?_ ?_)
    · exact fun h ↦ Set.notMem_empty i (h1 ▸ (h : i ∈ posSupport v))
    · exact fun h ↦ Set.notMem_empty i (h2 ▸ (h : i ∈ negSupport v))
  -- Step C: the family `-t ::ₘ M'` sums to zero
  set M' := M.filter (· ≠ 0) with hM'
  have hmem : ∀ x ∈ -t ::ₘ M', x = -t ∨ x ∈ M' := fun x hx ↦ Multiset.mem_cons.1 hx
  have hbal : comparisonSum (-t ::ₘ M') = 0 := funext fun i ↦ by
    rw [comparisonSum_cons, hM', comparisonSum_filter_ne_zero, hsum, Pi.neg_apply,
      SignType.coe_neg, neg_add_cancel, Pi.zero_apply]
  have hpos : ∀ x ∈ -t ::ₘ M', (posSupport x).Nonempty := by
    intro x hx
    rcases hmem x hx with rfl | hx
    · rwa [posSupport_neg]
    · exact h0 x (Multiset.mem_of_mem_filter hx) (by simpa using Multiset.of_mem_filter hx)
  have hmerge : ∀ x ∈ -t ::ₘ M', ∀ y ∈ -t ::ₘ M', x ≠ y → ¬Mergeable x y := by
    intro x hx y hy hxy hm
    rcases hmem x hx with rfl | hx <;> rcases hmem y hy with rfl | hy
    · exact hxy rfl
    · exact hrd ⟨y, Multiset.mem_of_mem_filter hy, hm⟩
    · exact hrd ⟨x, Multiset.mem_of_mem_filter hx, hm.symm⟩
    · have hxM := Multiset.mem_of_mem_filter hx
      have hyx : y ∈ M.erase x :=
        (Multiset.mem_erase_of_ne hxy.symm).2 (Multiset.mem_of_mem_filter hy)
      exact hnogm ⟨x, y, (M.erase x).erase y,
        by rw [Multiset.cons_erase hyx, Multiset.cons_erase hxM], hm⟩
  obtain ⟨x, hxS, y, hyS, hxy, had1, had2⟩ :=
    exists_antiDominating (by simpa using hn) hbal hpos hmerge (Multiset.cons_ne_zero)
  -- `-t` is excluded by `hnotdom`, so the pair comes from `M` and is a null pair
  rcases hmem x hxS with rfl | hx <;> rcases hmem y hyS with rfl | hy
  · exact (hxy rfl).elim
  · rw [posSupport_neg] at had1; rw [negSupport_neg] at had2
    exact (hnotdom y (Multiset.mem_of_mem_filter hy) had2 had1).elim
  · rw [posSupport_neg] at had2; rw [negSupport_neg] at had1
    exact (hnotdom x (Multiset.mem_of_mem_filter hx) had1 had2).elim
  · have hle (i) : (x i : ℤ) + y i ≤ 0 :=
      add_nonpos_of_imp (x i) (y i) (fun h ↦ had1 h) (fun h ↦ had2 h)
    refine Or.inl ⟨x, Multiset.mem_of_mem_filter hx, y, Multiset.mem_of_mem_filter hy, hle, ?_⟩
    by_contra! hge
    exact hmerge x hxS y hyS hxy <| mergeable_iff.mpr fun i hxyi ↦
      eq_zero_of_add_eq_zero_of_eq (x i) (y i) ((hle i).antisymm (hge i)) hxyi

private lemma merge_residual_aux (a b : SignType) (h : -a = b → -a = 0) :
    SignType.sign ((SignType.sign ((a : ℤ) + (-b : SignType)) : ℤ) + b) = a := by decide +revert

private lemma mergeable_residual_aux (a b : SignType) (h : -a = b → -a = 0) :
    SignType.sign ((a : ℤ) + (-b : SignType)) = b →
      SignType.sign ((a : ℤ) + (-b : SignType)) = 0 := by decide +revert

private lemma recombine [IsQualitativeProbability r] {t v : Fin n → SignType}
    (hm : Mergeable (-t) v) (hv : r (posSupport v) (negSupport v))
    (hX : r (posSupport (merge t (-v))) (negSupport (merge t (-v)))) :
    r (posSupport t) (negSupport t) := by
  have hm' : Mergeable (merge t (-v)) v := mergeable_iff.mpr fun i ↦ by
    have := mergeable_iff.mp hm i
    simp only [Pi.neg_apply] at this
    exact mergeable_residual_aux (t i) (v i) this
  have := merge_valid hX hv hm'
  have e : merge (merge t (-v)) v = t := funext fun i ↦ by
    have := mergeable_iff.mp hm i
    simp only [Pi.neg_apply] at this
    exact merge_residual_aux (t i) (v i) this
  rwa [e] at this

private theorem merge_to_single (hn : n ≤ 4) (r : Set (Fin n) → Set (Fin n) → Prop)
    [IsQualitativeProbability r] (hnull : ∀ i, ¬ r ∅ {i})
    (M : Multiset (Fin n → SignType)) (hvalid : ∀ v ∈ M, r (posSupport v) (negSupport v))
    (t : Fin n → SignType) (hsum : ∀ i, comparisonSum M i = t i) :
    r (posSupport t) (negSupport t) := by
  by_cases hne : (negSupport t).Nonempty
  · by_cases hdom : ∃ v ∈ M, posSupport v ⊆ posSupport t ∧ negSupport t ⊆ negSupport v
    · -- mono-domination discharge
      obtain ⟨v, hvM, hv1, hv2⟩ := hdom
      exact trans_of r (mono _ _ hv1) (trans_of r (hvalid v hvM) (mono _ _ hv2))
    · -- no mono-dominating member: either a mergeable pair (merge & recurse) or,
      -- failing that, a forced null atom contradicting `hnull`.
      push Not at hdom
      by_cases hgm : ∃ v w rest, M = v ::ₘ w ::ₘ rest ∧ Mergeable v w
      case neg =>
        rcases v1_tailored hn M hsum hne hdom hgm with
          ⟨v, hvM, w, hwM, hle, i0, hlt⟩ | ⟨v, hvM, hm⟩
        · -- null pair → null atom → contradicts hnull
          obtain ⟨i, hi⟩ := null_from_pair (hvalid v hvM) (hvalid w hwM) hle i0 hlt
          exact absurd hi (hnull i)
        · -- reversed target merges `v`: peel `v`, recurse on the residual, recombine
          have hmt : Mergeable t (-v) := ⟨by simpa using hm.2, by simpa using hm.1⟩
          have hsum' : ∀ i, comparisonSum (M.erase v) i = merge t (-v) i := fun i ↦ by
            have h1 := hsum i
            rw [← Multiset.cons_erase hvM, comparisonSum_cons] at h1
            rw [coe_merge hmt, Pi.neg_apply, SignType.coe_neg]
            omega
          exact recombine hm (hvalid v hvM) (merge_to_single hn r hnull (M.erase v)
            (fun x hx ↦ hvalid x (Multiset.mem_of_mem_erase hx)) (merge t (-v)) hsum')
      obtain ⟨v, w, rest, hM, hm⟩ := hgm
      -- new family: `merge v w ::ₘ rest`, one smaller
      have hvalid' : ∀ x ∈ merge v w ::ₘ rest, r (posSupport x) (negSupport x) := by
        intro x hx
        rcases Multiset.mem_cons.mp hx with rfl | hx
        · exact merge_valid (hvalid v (by simp [hM])) (hvalid w (by simp [hM])) hm
        · exact hvalid x (by simp [hM, hx])
      have hsum' : ∀ i, comparisonSum (merge v w ::ₘ rest) i = t i := fun i ↦ by
        rw [comparisonSum_cons, coe_merge hm, ← hsum i, hM]
        simp only [comparisonSum_cons]; omega
      exact merge_to_single hn r hnull (merge v w ::ₘ rest) hvalid' t hsum'
  · -- trivial-target discharge: `negSupport t = ∅`
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    exact rel_empty _
termination_by Multiset.card M
decreasing_by
  all_goals first
    | exact Multiset.card_erase_lt_of_mem ‹_›
    | (rw [‹M = _›]; simp)

/-- A qualitative probability on at most four atoms with no null atom satisfies cancellation, by
    the merge reduction `merge_to_single`. -/
theorem no_null_cancellation (hn : n ≤ 4) (r : Set (Fin n) → Set (Fin n) → Prop)
    [IsQualitativeProbability r] (hnull : ∀ i, ¬ r ∅ {i}) : Cancellation r := by
  intro M hvalid hsum v hv
  rw [← posSupport_neg v, ← negSupport_neg v]
  refine merge_to_single hn r hnull (M.erase v)
    (fun w hw ↦ hvalid w (Multiset.mem_of_mem_erase hw)) (-v) fun i ↦ ?_
  have h := congrFun hsum i
  rw [← Multiset.cons_erase hv, comparisonSum_cons, Pi.zero_apply] at h
  rw [Pi.neg_apply, SignType.coe_neg]
  omega

/-- Every qualitative probability on at most four atoms satisfies cancellation. A null atom
    reduces to one atom fewer (`cancellation_of_null_atom`); otherwise the merge reduction
    applies. -/
theorem cancellation_of_le_four : ∀ {n : ℕ}, n ≤ 4 →
    ∀ (r : Set (Fin n) → Set (Fin n) → Prop) [IsQualitativeProbability r], Cancellation r
  | 0, _, r, hr => (not_isQualitativeProbability_of_isEmpty r hr).elim
  | 1, hn, r, _ => no_null_cancellation hn r fun i hi ↦ by
      obtain ⟨j, hj⟩ := exists_not_rel_empty_singleton r
      exact hj (Subsingleton.elim i j ▸ hi)
  | n + 2, hn, r, _ => by
      by_cases h : ∃ j, r ∅ {j}
      · obtain ⟨j, hj⟩ := h
        exact cancellation_of_null_atom r hj fun r' _ ↦
          cancellation_implies_representable r' (cancellation_of_le_four (by omega) r')
      · push Not at h
        exact no_null_cancellation hn r h

end ComparativeProbability
